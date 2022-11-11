module Language.Reflection.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import public Language.Reflection.Syntax
import public Language.Reflection
import public Data.Vect

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
Res : Type -> Type
Res = Either String

--------------------------------------------------------------------------------
--          General Types
--------------------------------------------------------------------------------

||| Constructor of a data type
public export
record Con n where
  constructor MkCon
  name     : Name
  args     : List NamedArg
  typeArgs : Vect n TTImp

||| True if the given constructor has only erased arguments.
public export
isConstant : Con n -> Bool
isConstant = all isErased . args

tcArgs :
     Elaboration m
  => Name
  -> Vect k TTImp
  -> (n : Nat)
  -> TTImp
  -> m (Vect (k + n) TTImp)
tcArgs _  ts 0     t@(IVar _ _) =
  pure (rewrite plusZeroRightNeutral k  in ts)
tcArgs nm ts (S x) (IApp _ s t) =
  rewrite sym $ plusSuccRightSucc k x in tcArgs nm (t :: ts) x s
tcArgs nm _  _    _             =
  fail "Unexpected type for constructor \{nm}"

||| Tries to lookup a data constructor by name, returning it together
||| with the arity of the corresponding type constructor.
export
getCon : Elaboration m => Name -> m (n ** Con n)
getCon nm = do
  (nm',tt)       <- lookupName nm
  (args,tpe)     <- unPiNamed tt
  case unApp tpe of
    (IVar _ _, as) => pure $ (_ ** MkCon nm' args (Vect.fromList as))
    _              => fail "Unexpected type for constructor \{nm}"

||| Tries to lookup a data constructor for a type constructor of
||| the given arity.
export
getConN : Elaboration m => (n : Nat) -> Name -> m (Con n)
getConN n nm = do
  (nm',tt)   <- lookupName nm
  (args,tpe) <- unPiNamed tt
  as         <- tcArgs nm' [] n tpe
  pure $ MkCon nm' args (reverse as)

||| Information about a data type
|||
||| @name : Name of the data type
|||         Note: There is no guarantee that the name will be fully
|||         qualified
||| @args : Type arguments of the data type
||| @cons : List of data constructors
public export
record TypeInfo where
  constructor MkTypeInfo
  name : Name
  arty : Nat
  args : Vect arty NamedArg
  cons : List (Con arty)

||| True if the given type has only constant constructors and
||| is therefore represented by a single unsigned integer at runtime.
public export
isEnum : TypeInfo -> Bool
isEnum ti = all isConstant $ ti.cons

||| True if the given type has a single constructor with a single
||| unerased argument.
public export
isNewtype : TypeInfo -> Bool
isNewtype (MkTypeInfo _ _ _ [c]) = count (not . isErased) c.args == 1
isNewtype _                      = False

||| True if the given type has a single constructor with only erased
||| arguments. Such a value will have a trivial runtime representation.
public export
isErased : TypeInfo -> Bool
isErased (MkTypeInfo _ _ _ [c]) = isConstant c
isErased _                      = False

||| Tries to get information about the data type specified
||| by name. The name need not be fully qualified, but
||| needs to be unambiguous.
export
getInfo' : Elaboration m => Name -> m TypeInfo
getInfo' n =
  do (n',tt)        <- lookupName n
     (args,IType _) <- unPiNamed tt
                    | (_,_) => fail "Type declaration does not end in IType"

     let (arty ** argsv) := (length args ** Vect.fromList args)

     conNames       <- getCons n'
     cons           <- traverse (getConN arty) conNames
     pure (MkTypeInfo n' arty argsv cons)

||| macro version of `getInfo'`
export %macro
getInfo : Name -> Elab TypeInfo
getInfo = getInfo'

||| Tries to get the name of the sole constructor
||| of data type specified by name. Fails, if
||| the name is not unambiguous, or if the data type
||| in question has not exactly one constructor.
export %macro
singleCon : Name -> Elab Name
singleCon n = do (MkTypeInfo _ _ _ cs) <- getInfo' n
                 (c::Nil) <- pure cs | _ => fail "not a single constructor"
                 pure $ name c

--------------------------------------------------------------------------------
--          Parameterized Types
--------------------------------------------------------------------------------

||| Explicit arg of a data constructor
|||
||| The `hasParam` flag indicates, whether one of the
||| type parameters of the data type makes an appearance
||| in the arguments type.
|||
||| For instance, in the following data type, arguments
||| a1 and a3 would have `hasParam` set to `True`.
|||
||| ```
|||   data MyData : (f : Type -> Type) -> (t : Type) -> Type where
|||     A : (a1 : f Int) -> (a2 : String) -> MyData f a
|||     B : (a3 : f a)   -> MyData f a
||| ```
public export
record ExplicitArg where
  constructor MkExplicitArg
  ||| Name of the argument
  name        : Name

  ||| Argument's type as a `TTImp` tree
  tpe         : TTImp

  ||| List of types occuring in `tpe` whose outermost
  ||| type constructor is a parameter.
  |||
  ||| Two examples:
  |||   If `tpe` is `Foo a (Maybe b)`, this is `[a,b]`
  |||   if `tpe` is `Bar (f Int) c`, this is `[f Int,c]`
  paramTypes  : List TTImp

  ||| True if the name of the data type itself
  ||| makes an appearance in `tpe`
  isRecursive : Bool

||| Constructor of a parameterized data type.
|||
||| We only accept two types of arguments for
||| such a constructor: Implicit arguments
||| corresponding to the parameters of the data types
||| and explicit arguments.
|||
||| See `ParamTypeInfo` for examples about what is
||| allowed and what not.
public export
record ParamCon where
  constructor MkParamCon
  name         : Name
  explicitArgs : List ExplicitArg

||| Information about a parameterized data type.
|||
||| The constructors of such a data type are only
||| allowed to have two kinds of arguments:
||| Implicit arguments corresponding to the data
||| type's parameters and explicit arguments.
|||
||| Auto implicits or existentials are not allowed.
|||
||| Below are some examples of valid parameterized data types
|||
||| ```
||| data Foo a = Val a | Nope
|||
||| data Reader : (m : Type -> Type) -> (e : Type) -> (a : Type) -> Type where
|||   MkReader : (run : e -> m a) -> Reader m e a
|||
||| data Wrapper : (n : Nat) -> (t : Type) -> Type
|||   Wrap : Vect n t -> Wrapper n t
||| ```
|||
||| Examples of invalid parameterized data types
|||
||| Indexed types families:
|||
||| ```
||| data GADT : (t : Type) -> Type where
|||   A : GADT Int
|||   B : GADT ()
|||   Any : a -> GADT a
||| ```
|||
||| Existentials:
|||
||| ```
||| data Forget : Type where
|||  DoForget : a -> Forget
||| ```
|||
||| Constraint types:
|||
||| ```
||| data ShowableForget : Type where
|||  ShowForget : Show a => a -> Forget
||| ```
public export
record ParamTypeInfo where
  constructor MkParamTypeInfo
  name   : Name
  params : List (Name,TTImp)
  cons   : List ParamCon

||| Given the constructor arguments of a data type, returns
||| the list of those argument types, in which at least one
||| of the data type's parameters makes an appearance.
|||
||| This function uses a rudimentary comparison to make
||| sure that the returned list contains only distinct types.
|||
||| This function is used to calculate the list of required constraints
||| when automatically deriving interface implementations.
export
calcArgTypesWithParams : ParamTypeInfo -> List TTImp
calcArgTypesWithParams = nubBy sameType . concatMap types . cons
  where types : ParamCon -> List TTImp
        types c = c.explicitArgs >>= paramTypes

        sameType : TTImp -> TTImp -> Bool
        sameType (IVar _ x)   (IVar _ a)   = x == a
        sameType (IApp _ x y) (IApp _ a b) = sameType x a && sameType y b
        sameType _ _                       = False


-- tries to extract the type parameter names
-- from a constructor's type args
private
conParams : (con : Name) -> Vect n TTImp -> Res $ Vect n Name
conParams con ts = maybe err Right $ traverse unVar ts
  where err : Res a
        err = Left "\{con} has non parameter type arguments"

private
sameArgName : (dataType : Name) -> (arg : Name) -> Bool
sameArgName = (==)

private total
inspect : (dataType : Name)
        -> Vect n (Name,Name)
        -> TTImp
        -> (TTImp, List TTImp, Bool)
inspect dt ns x = let (t,ts,_,b) = run x
                   in (t,ts,b)
        -- First Bool: outer-most type constructor is parameter
        -- Second Bool: expression contains data type name
  where run : TTImp -> (TTImp,List TTImp,Bool,Bool)
        run (IVar x n) =
          case lookup n ns of
            Nothing => (IVar x n, Nil, False, sameArgName dt n)
            Just n' => let t = IVar x n'
                        in (t,[t],True,False)

        run (IPi x y z w a r) =
          let (a',as,_,ca) = run a
              (r',rs,_,cr) = run r
           in (IPi x y z w a' r', as ++ rs, False, ca || cr)

        run (IApp x y z) =
          let (y',ys,b,cy) = run y
              (z',zs,_,cz) = run z
              c             = cy || cz
              t             = IApp x y' z'
           in if cy || cz then (t, ys ++ zs, b, True)
              else if b then (t, [t], b, False)
              else (t, ys ++ zs, False, False)

        run t = (t,Nil,False,False)

private
implicitErr : (con: Name) -> (n : Name) -> Res a
implicitErr con n = Left $  show con
                         ++ ": Non-explicit constructor argument \""
                         ++ show n
                         ++ "\" is not a type parameter."

private
indicesErr : (con : Name) -> (ns : Vect k Name) -> Res a
indicesErr con ns = Left $ show con ++ ": Type indices found: " ++ show ns

-- For a constructor, takes a list of type parameter
-- names and tries to remove the corresponding erased implicit
-- arguments from the head of the given argument list.
-- Extracts explicit argument names and types from the rest of
-- the list.
--
-- Fails if : a) Not all values in `names` are present as implicit
--               function arguments
--            b) The function has additional non-implicit arguments
private
argPairs :  (dataType : Name)
         -> (con : Name)
         -> Vect n (Name,Name)
         -> List NamedArg
         -> Res $ List ExplicitArg
argPairs dt con names = run names
  where delete : Name -> Vect (S k) (Name,a) -> Res $ Vect k (Name,a)
        delete m ((n,a) :: ns)  =
          if m == n then Right ns
                    else case ns of
                              []        => implicitErr con m
                              ns@(_::_) => ((n,a) ::) <$> delete m ns

        mkArg : NamedArg -> Res ExplicitArg
        mkArg (MkArg _ ExplicitArg n t) = let (t',ts,isD) = inspect dt names t
                                           in Right $ MkExplicitArg n t' ts isD
        mkArg (MkArg _ _ n _)           = implicitErr con n

        run : Vect k (Name,a) -> List NamedArg -> Res $ List ExplicitArg
        run [] as = traverse mkArg as
        run ps@(_::_) ((MkArg _ ImplicitArg n _) :: t) = run !(delete n ps) t
        run ps _ = indicesErr con (map fst ps)


private
paramCon : (dt : Name) -> Vect n Name -> Con n -> Res $ ParamCon
paramCon dt ns (MkCon nm as t) = do
  params <- conParams nm t
  args   <- argPairs dt nm (zip params ns) as
  pure $ MkParamCon nm args

private
toParamTypeInfo : TypeInfo -> Res ParamTypeInfo
toParamTypeInfo (MkTypeInfo n arty as cs) =
  do ps  <- traverse expPair as
     let ns := map fst ps
     cs' <- traverse (paramCon n ns) cs
     pure $ MkParamTypeInfo n (toList ps) cs'
  where expPair : NamedArg -> Res (Name,TTImp)
        expPair  (MkArg _ ExplicitArg n t) = Right (n,t)
        expPair _ = Left $  show n
                         ++ ": Non-explicit type arguments are not supported"

||| Returns information about a parameterized data type
||| specified by the given (probably not fully qualified) name.
|||
||| The implementation makes sure, that all occurences of
||| type parameters in the constructors have been given
||| the same names as occurences in the type declaration.
export
getParamInfo' : Elaboration m => Name -> m ParamTypeInfo
getParamInfo' n = do ti         <- getInfo' n
                     (Right pt) <- pure (toParamTypeInfo ti)
                                | (Left err) => fail err
                     pure pt

||| macro version of `getParamInfo`.
export %macro
getParamInfo : Name -> Elab ParamTypeInfo
getParamInfo = getParamInfo'
