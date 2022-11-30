||| Utility types and functions for automatically deriving
||| interface instances. So far, this module does not provide
||| deriving functions for existing interfaces. See
||| Doc.Generic4 for examples, how this could be done
||| using the functionality provided here.
module Language.Reflection.Derive

import Decidable.Equality
import Data.DPair
import public Language.Reflection.Syntax
import public Language.Reflection.Types

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Elaborateable
--------------------------------------------------------------------------------

||| Interface for named things that can be looked up by name using
||| elaborator reflection.
public export
interface Named a => Elaborateable a where
  find_ : Elaboration m => Name -> m a

||| Utility version of `find_` taking an explicit type argument.
public export %inline
find : (0 a : Type) -> Elaborateable a => Elaboration m => Name -> m a
find _ = find_

export %inline
Elaborateable TypeInfo where
  find_ = getInfo'

export %inline
Elaborateable ParamTypeInfo where
  find_ = getParamInfo'

public export %inline
Named a => Named (Subset a p) where
  (.getName) (Element v _) = v.getName

--------------------------------------------------------------------------------
--          Names
--------------------------------------------------------------------------------

||| Generates the name of a function implementing some functionality
||| for the given type.
export
funName : Named a => a -> String -> Name
funName n fun = UN $ Basic $ fun ++ n.nameStr

||| Generates the name of an interface's implementation function
export
implName : Named a => a -> String -> Name
implName n iface = UN $ Basic $ "impl" ++ iface ++ n.nameStr

--------------------------------------------------------------------------------
--          Arguments
--------------------------------------------------------------------------------

||| A single constructor argument, for which we have `n` bound
||| variables on the left hand side of a pattern match clause, and
||| which is refined by predicate `p`.
public export
record BoundArg (n : Nat) (p : Arg -> Type) where
  constructor BA
  arg  : Arg
  vars : Vect n Name
  prf  : p arg

public export
split : Vect k (Vect (S n) a) -> (Vect k a, Vect k (Vect n a))
split []                 = ([],[])
split ((x :: xs) :: yss) =
  let (zs,zss) := split yss
   in (x :: zs, xs :: zss)

||| Refine a list of constructor arguments with the given predicate
||| and pair them with a number of bound variable names.
export
boundArgs :
     {0 p : Arg -> Type}
  -> (f : (a : Arg) -> Maybe (p a))
  -> Vect n Arg
  -> Vect k (Vect n Name)
  -> SnocList (BoundArg k p)
boundArgs f = go Lin
  where go :  SnocList (BoundArg k p)
           -> Vect m Arg
           -> Vect k (Vect m Name)
           -> SnocList (BoundArg k p)
        go sx (x :: xs) ns =
          let (y, ys) := split ns
           in case f x of
                Just prf => go (sx :< BA x y prf) xs ys
                Nothing  => go sx xs ys
        go sx []        _  = sx

public export
data Explicit : Arg -> Type where
  IsExplicit : Explicit (MkArg c ExplicitArg n t)

public export
explicit : (a : Arg) -> Maybe (Explicit a)
explicit (MkArg _ ExplicitArg _ _) = Just IsExplicit
explicit _                         = Nothing

public export
data NamedArg : Arg -> Type where
  IsNamed : NamedArg (MkArg c p (Just n) t)

public export
named : (a : Arg) -> Maybe (NamedArg a)
named (MkArg _ _ (Just n) _) = Just IsNamed
named _                      = Nothing

public export
argName : (a : Arg) -> {auto 0 prf : NamedArg a} -> Name
argName (MkArg _ _ (Just n) _) {prf = IsNamed} = n

public export
data Unerased : Arg -> Type where
  U1 : Unerased (MkArg M1 p n t)
  UW : Unerased (MkArg MW p n t)

public export
unerased : (a : Arg) -> Maybe (Unerased a)
unerased (MkArg M0 _ _ _) = Nothing
unerased (MkArg M1 _ _ _) = Just U1
unerased (MkArg MW _ _ _) = Just UW

public export
data Erased : Arg -> Type where
  IsErased : Erased (MkArg M0 p n t)

public export
erased : (a : Arg) -> Maybe (Erased a)
erased (MkArg M0 _ _ _) = Just IsErased
erased _                = Nothing

public export
0 Regular : Arg -> Type
Regular a = (Unerased a, Explicit a)

public export
regular : (a : Arg) -> Maybe (Regular a)
regular a = [| MkPair (unerased a) (explicit a) |]

public export
0 RegularNamed : Arg -> Type
RegularNamed a = (NamedArg a, Regular a)

public export
regularNamed : (a : Arg) -> Maybe (RegularNamed a)
regularNamed a = [| MkPair (named a) (regular a) |]

public export
0 NamedExplicit : Arg -> Type
NamedExplicit a = (NamedArg a, Explicit a)

public export
namedExplicit : (a : Arg) -> Maybe (NamedExplicit a)
namedExplicit a = [| MkPair (named a) (explicit a) |]

public export
toNamed : BoundArg n p -> Maybe (BoundArg n (\a => (NamedArg a, p a)))
toNamed (BA arg vars prf) = case named arg of
  Just v  => Just (BA arg vars (v, prf))
  Nothing => Nothing

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Tries to lookup and refine an elaboratable value based on the
||| given predicate.
public export
refine :
     {0 p : a -> Type}
  -> Elaboration m
  => Elaborateable a
  => ((v : a) -> Res (p v))
  -> Name
  -> m (Subset a p)
refine f nm = do
  v <- find a nm
  case f v of
    Right prf => pure $ Element v prf
    Left err  => fail "Error when refining \{nm}: \{err}"

--------------------------------------------------------------------------------
--          Deriving Implementations
--------------------------------------------------------------------------------

||| A top-level declaration plus its definition.
public export
record TopLevel where
  constructor TL
  claim : Decl
  defn  : Decl

||| Creates a function declaration with a `%hint` and `%inline`
||| annotation.
|||
||| This is what you want if you use separate top-level function
||| for the interface's implementation and the actual implementation
||| just adds those functions to the interface constructor.
public export %inline
implClaim : Name -> TTImp -> Decl
implClaim = interfaceHintOpts Public [Inline]

||| Creates the function type for an interface implementation including
||| the required implicit and auto-implicit arguments.
|||
||| For instance, if `Name` is `"Eq"` and the data type in question is
||| `Either` with parameter names `a` and `b`, the `TTImp` returned
||| corresponds to
|||
||| ```idris
||| {0 a : _} -> {0 b : _} -> Eq a => Eq b => Eq (Either a b)`
||| ```
export
implType : Name -> ParamTypeInfo -> TTImp
implType n p = piAll (var n .$ p.applied) (allImplicits p n)

||| Extracts the innermost target of a function application.
||| For instance, for `Foo @{bar} baz {n = 12}`, this will extract `Foo`.
export
unAppAny : TTImp -> TTImp
unAppAny (IApp fc s t)         = unAppAny s
unAppAny (INamedApp fc s nm t) = unAppAny s
unAppAny (IAutoApp fc s t)     = unAppAny s
unAppAny (IWithApp fc s t)     = unAppAny s
unAppAny t                     = t

||| Tries to extract the result type from the current goal when
||| deriving custom interface implementations.
|||
||| For instance, if the goal type is `Eq (Either a b)`, this
||| returns a `TTImp` corresponding to `Either a b` plus the
||| name of the data constructor `Either`.
export
extractResult : TTImp -> Maybe (TTImp, Name)
extractResult (IApp _ _ tpe) = case unAppAny tpe of
  IVar _ nm => Just (tpe, nm)
  _         => Nothing
extractResult _              = Nothing

||| Generates (potentially mutually recursive) declarations and
||| definitions by looking up the given names and converting them
||| to toplevel definitions.
|||
||| All claims will be declared first, so that we support mutually
||| recursive definitions.
|||
||| The list of resolved names is passed together with the resolved
||| values to the function generating the desired toplevel definitions.
export
deriveGeneral :
     Elaboration m
  => Elaborateable t
  => List Name
  -> List (List Name -> t -> List TopLevel)
  -> m ()
deriveGeneral ns fs = do
  pts <- traverse (find t) ns
  let names  := map (.getName) pts
      tls    := fs >>= \f => pts >>= f names
      claims := map claim tls
      defns  := map defn tls

  logMsg "derive.claims" 1 $ unlines (map show claims)
  logMsg "derive.definitions" 1 $ unlines (map show defns)
  declare $ claims ++ defns

||| Allows the derivation of mutually dependant interface
||| implementations by first defining type declarations before
||| declaring implementations.
|||
||| Note: There is no need to call this from withi a `mutual` block.
export %inline
deriveMutual :
     Elaboration m
  => List Name
  -> List (List Name -> ParamTypeInfo -> List TopLevel)
  -> m ()
deriveMutual = deriveGeneral

||| Given a name of a parameterized data type plus a list of
||| interface generation functions, tries
||| to implement these interfaces automatically using
||| elaborator reflection.
|||
||| Again, see Doc.Generic4 for a tutorial and examples how
||| to use this.
export %inline
derive :
     Elaboration m
  => Name
  -> List (List Name -> ParamTypeInfo -> List TopLevel)
  -> m ()
derive n = deriveMutual [n]

--------------------------------------------------------------------------------
--          Interface Factories
--------------------------------------------------------------------------------

||| Like `MkEq` but generates (/=) from the passed `eq` function.
public export %inline
mkEq : (eq : a -> a -> Bool) -> Eq a
mkEq eq = MkEq eq (\a,b => not $ eq a b)

||| Creates an `Ord` value from the passed comparison function
||| using default implementations based on `comp` for all
||| other function.
public export
mkOrd : Eq a => (comp : a -> a -> Ordering) -> Ord a
mkOrd comp =
  MkOrd comp
    (\a,b => comp a b == LT)
    (\a,b => comp a b == GT)
    (\a,b => comp a b /= GT)
    (\a,b => comp a b /= LT)
    (\a,b => if comp a b == GT then a else b)
    (\a,b => if comp a b == LT then a else b)

||| Creates a `Show` value from the passed `show` functions.
public export
mkShow : (show : a -> String) -> Show a
mkShow show = MkShow show (\_ => show)

||| Creates a `Show` value from the passed `showPrec` functions.
public export
mkShowPrec : (showPrec : Prec -> a -> String) -> Show a
mkShowPrec showPrec = MkShow (showPrec Open) showPrec

||| Creates a `DecEq` value from the passed implementation function
||| for `decEq`
public export
mkDecEq : (decEq : (x1 : a) -> (x2 : a) -> Dec (x1 = x2)) -> DecEq a
mkDecEq = %runElab check (var $ singleCon "DecEq")
