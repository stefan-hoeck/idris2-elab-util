||| Utility types and functions for automatically deriving
||| interface instances. So far, this module does not provide
||| deriving functions for existing interfaces. See
||| Doc.Generic4 for examples, how this could be done
||| using the functionality provided here.
module Language.Reflection.Derive

import Decidable.Equality
import public Data.DPair
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
  vars : Vect n String
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
  -> Vect k (Vect n String)
  -> SnocList (BoundArg k p)
boundArgs f = go Lin
  where go :  SnocList (BoundArg k p)
           -> Vect m Arg
           -> Vect k (Vect m String)
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
  IsNamed : NamedArg (MkArg c p (Just (UN $ Basic n)) t)

public export
named : (a : Arg) -> Maybe (NamedArg a)
named (MkArg _ _ (Just $ UN $ Basic n) _) = Just IsNamed
named _                                   = Nothing

public export
argName : (a : Arg) -> {auto 0 prf : NamedArg a} -> Name
argName (MkArg _ _ (Just $ UN $ Basic n) _) {prf = IsNamed} = UN $ Basic n

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

export
failRecord : String -> Res a
failRecord s =
  Left "Interface \{s} can only be derived for single-constructor data types"

||| Generates a pattern clause for accumulating the arguments
||| of a singled data constructor.
|||
||| This is used, for instance, to implement `showPrec`, when
||| deriving `Show` implementations.
|||
||| @ p   : The predicate used to refine the constructor's arguments
|||
||| @ f   : Refining function.
|||
||| @ lhs : Adjusts the left-hand side of the clause.
|||         The argument corresponds to the constructor with
|||         all explicit arguments bound to variables named
|||         `x0`, `x1` etc.
|||
||| @ rhs : Adjusts the right-hand side of the clause.
|||         The `SnocList` contains the arguments, as transformed
|||         by `arg`.
|||
||| @ arg : Processes a single argument
|||
||| @ con : The constructor to process.
export
accumArgs :
     {0 p : Arg -> Type}
  -> (f : (a : Arg) -> Maybe (p a))
  -> (lhs : TTImp -> TTImp)
  -> (rhs : SnocList TTImp -> TTImp)
  -> (arg : BoundArg 1 p -> TTImp)
  -> (con : Con n vs)
  -> Clause
accumArgs f lhs rhs arg c =
  let xs := freshNames "x" c.arty
      cx := bindCon c xs
      sx := map arg (boundArgs f c.args [xs])
   in lhs cx .= rhs sx

||| Generates a pattern clause for accumulating the arguments
||| of two equivalent data constructors.
|||
||| This is used, for instance, to implement `(==)`, when
||| deriving `Eq` implementations.
|||
||| @ p   : The predicate used to refine the constructor's arguments
|||
||| @ f   : Refining function.
|||
||| @ lhs : Adjusts the left-hand side of the clause.
|||         The first argument corresponds to the constructor with
|||         all explicit arguments bound to variables named
|||         `x0`, `x1` etc., the second to the constructor
|||         with bound explicit arguments namd `y0`, `y1` etc.
|||
||| @ rhs : Adjusts the right-hand side of the clause.
|||         The `SnocList` contains the arguments, as transformed
|||         by `arg`.
|||
||| @ arg : Processes a single pair of arguments
|||
||| @ con : The constructor to process.
export
accumArgs2 :
     {0 p : Arg -> Type}
  -> (f : (a : Arg) -> Maybe (p a))
  -> (lhs : TTImp -> TTImp -> TTImp)
  -> (rhs : SnocList TTImp -> TTImp)
  -> (arg : BoundArg 2 p -> TTImp)
  -> (con : Con n vs)
  -> Clause
accumArgs2 f lhs rhs arg c =
  let xs := freshNames "x" c.arty
      ys := freshNames "y" c.arty
      cx := bindCon c xs
      cy := bindCon c ys
      sx := map arg (boundArgs f c.args [xs,ys])
   in lhs cx cy .= rhs sx

||| Generates a pattern clause for mapping the arguments
||| of a data constructors over a unary function.
|||
||| This is used, for instance, to implement `abs`, when
||| deriving `Abs` implementations.
|||
||| @ p   : The predicate used to refine the constructor's arguments
|||
||| @ f   : Refining function.
|||
||| @ lhs : Adjusts the left-hand side of the clause.
|||         The argument corresponds to the constructor with
|||         all explicit arguments bound to variables named
|||         `x0`, `x1` etc.
|||
||| @ arg : Processes a single argument
|||
||| @ con : The constructor to process.
export
mapArgs :
     {0 p : Arg -> Type}
  -> (f : (a : Arg) -> Maybe (p a))
  -> (lhs : TTImp -> TTImp)
  -> (arg : BoundArg 1 p -> TTImp)
  -> (con : Con n vs)
  -> Clause
mapArgs f lhs arg c =
  let xs := freshNames "x" c.arty
      cx := bindCon c xs
      sx := map arg (boundArgs f c.args [xs])
   in lhs cx .= appAll c.name (sx <>> [])

||| Generates a pattern clause for mapping the arguments
||| of two data constructors over a binary function.
|||
||| This is used, for instance, to implement `(+)`, when
||| deriving `Num` implementations.
|||
||| @ p   : The predicate used to refine the constructor's arguments
|||
||| @ f   : Refining function.
|||
||| @ lhs : Adjusts the left-hand side of the clause.
|||         The first argument corresponds to the constructor with
|||         all explicit arguments bound to variables named
|||         `x0`, `x1` etc., the second to the constructor
|||         with bound explicit arguments namd `y0`, `y1` etc.
|||
||| @ arg : Processes a pair of arguments
|||
||| @ con : The constructor to process.
export
mapArgs2 :
     {0 p : Arg -> Type}
  -> (f : (a : Arg) -> Maybe (p a))
  -> (lhs : TTImp -> TTImp -> TTImp)
  -> (arg : BoundArg 2 p -> TTImp)
  -> (con : Con n vs)
  -> Clause
mapArgs2 f lhs arg c =
  let xs := freshNames "x" c.arty
      ys := freshNames "y" c.arty
      cx := bindCon c xs
      cy := bindCon c ys
      sx := map arg (boundArgs f c.args [xs,ys])
   in lhs cx cy .= appAll c.name (sx <>> [])

||| Generates a pattern clause for creating and applying
||| constructor arguments.
|||
||| This is used, for instance, to implement `fromInteger`, when
||| deriving `Num` implementations for record types.
|||
||| @ p   : The predicate used to refine the constructor's arguments
|||
||| @ f   : Refining function.
|||
||| @ arg : Processes a single argument
|||
||| @ con : The constructor to process.
export
injArgs :
     {0 p : Arg -> Type}
  -> (f : (a : Arg) -> Maybe (p a))
  -> (arg : BoundArg 0 p -> TTImp)
  -> (con : Con n vs)
  -> TTImp
injArgs f arg c =
  let sx := map arg (boundArgs f c.args [])
   in appAll c.name (sx <>> [])

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

export %inline
sequenceJoin : Applicative f => List (f $ List a) -> f (List a)
sequenceJoin = map join . sequence

public export
record ParamInfo where
  constructor PI
  name     : Name
  strategy : (n : Nat) -> Maybe (Exists $ ParamPattern n)
  goals    : List (List Name -> ParamTypeInfo -> Res (List TopLevel))

fromParamInfo : List Name -> TypeInfo -> ParamInfo -> Res (List TopLevel)
fromParamInfo nms ti (PI n f gs) = case f ti.arty of
  Just (Evidence _ pat) => do
    pti <- paramType ti pat
    map join $ traverse (\g => g nms pti) gs

  Nothing               => Left """
    Parameter pattern does not match type constructor arity (\{show ti.arty}).
    Note, that the arity includes implicit arguments, so those have to
    be considered in the pattern, too.
    """

export
deriveParam : Elaboration m => List ParamInfo -> m ()
deriveParam is = do
  ts <- traverse (find TypeInfo . name) is
  let ns := map (.getName) ts

  Right tls <- pure . map join . sequence $ zipWith (fromParamInfo ns) ts is
    | Left err => fail err

  let claims := map claim tls
      defns  := map defn tls

  logMsg "derive.claims" 1 $ unlines (map show claims)
  logMsg "derive.definitions" 1 $ unlines (map show defns)
  declare $ claims ++ defns

export
allParams : (n : Nat) -> Maybe (Exists $ ParamPattern n)
allParams n = Just $ Evidence _ $ paramsOnly n

export
allIndices : (n : Nat) -> Maybe (Exists $ ParamPattern n)
allIndices n = Just $ Evidence _ $ indicesOnly n

export
match : ParamPattern m k -> (n : Nat) -> Maybe (Exists $ ParamPattern n)
match p n = map (\v => Evidence _ v) $ go n p
  where
    go : (z : Nat) -> ParamPattern x y -> Maybe (ParamPattern z y)
    go 0 []           = Just []
    go (S j) (a :: b) = (a ::) <$> go j b
    go 0 (_ :: _)     = Nothing
    go (S j) []       = Nothing

export
deriveMutual :
     Elaboration m
  => List Name
  -> List (List Name -> ParamTypeInfo -> Res (List TopLevel))
  -> m ()
deriveMutual ns fs = deriveParam $ map (\n => PI n allParams fs) ns

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
  -> List (List Name -> ParamTypeInfo -> Res (List TopLevel))
  -> m ()
derive n = deriveMutual [n]

export %inline
deriveIndexed :
     Elaboration m
  => Name
  -> List (List Name -> ParamTypeInfo -> Res (List TopLevel))
  -> m ()
deriveIndexed n fs = deriveParam [PI n allIndices fs]

export %inline
derivePattern :
     Elaboration m
  => Name
  -> ParamPattern n k
  -> List (List Name -> ParamTypeInfo -> Res (List TopLevel))
  -> m ()
derivePattern n pat fs = deriveParam [PI n (match pat) fs]

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
