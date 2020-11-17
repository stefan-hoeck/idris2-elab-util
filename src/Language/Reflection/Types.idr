module Language.Reflection.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection
import Text.PrettyPrint.Prettyprinter

%language ElabReflection

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
Res : Type -> Type
Res = Either String

Eq Namespace where
  (MkNS xs) == (MkNS ys) = xs == ys

Eq Name where
  (UN a)   == (UN x)   = a == x
  (MN a b) == (MN x y) = a == x && b == y
  (NS a b) == (NS x y) = a == x && b == y
  (DN a b) == (DN x y) = a == x && b == y
  (RF a)   == (RF x)   = a == x
  _        == _        = False

--------------------------------------------------------------------------------
--          General Types
--------------------------------------------------------------------------------

||| Constructor of a data type
public export
record Con where
  constructor MkCon
  name : Name
  args : List NamedArg
  type : TTImp

||| Tries to lookup a constructor by name.
export
getCon : Name -> Elab Con
getCon n = do (n',tt)    <- lookupName n
              (args,tpe) <- unPiNamed tt
              pure $ MkCon n' args tpe

export
Pretty Con where
  prettyPrec p (MkCon n args tpe) = applyH p "MkCon" [n, args, tpe]


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
  args : List NamedArg
  cons : List Con

export
Pretty TypeInfo where
  pretty (MkTypeInfo name args cons) =
    let head = applyH Open "MkTypeInfo" [name, args]
        cons = indent 2 $ vsep (map pretty cons)
     in vsep [head,cons]

||| Tries to get information about the data type specified
||| by name. The name need not be fully qualified, but
||| needs to be unambiguous.
export
getInfo' : Name -> Elab TypeInfo
getInfo' n =
  do (n',tt)        <- lookupName n
     (args,IType _) <- unPiNamed tt
                    | (_,_) => fail "Type declaration does not end in IType"
     conNames       <- getCons n'
     cons           <- traverse getCon conNames
     pure (MkTypeInfo n' args cons)

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
singleCon n = do (MkTypeInfo _ _ cs) <- getInfo' n
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
  name     : Name
  tpe      : TTImp
  hasParam : Bool

export
Pretty ExplicitArg where
  prettyPrec p (MkExplicitArg n tpe hasParam) =
    applyH p "MkExplicitArg" [n, tpe, hasParam]

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

export
Pretty ParamCon where
  prettyPrec p (MkParamCon n explicitArgs) =
    applyH p "MkParamCon" [n, explicitArgs]

export
hasParamTypes : ParamCon -> List TTImp
hasParamTypes = mapMaybe hasParamType . explicitArgs
  where hasParamType : ExplicitArg -> Maybe TTImp
        hasParamType (MkExplicitArg _ t True) = Just t
        hasParamType _                        = Nothing

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
||| Examples of valid parameterized data types
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

export
Pretty ParamTypeInfo where
  pretty (MkParamTypeInfo name params cons) =
    let head = applyH Open "MkParamTypeInfo" [name, toList params]
        cons = indent 2 $ vsep (map pretty cons)
     in vsep [head,cons]

-- Given a Vect of type parameters (from the surrounding
-- data type), tries to extract a list of type parameter names
-- from the type declaration of a constructor.
private
conParams : (con : Name) -> Vect n a -> TTImp -> Res $ Vect n Name
conParams con as t = run as (snd $ unApp t)
  where err : String
        err = show con
            ++ ": Constructor type arguments do not match "
            ++ "data type type arguments."

        run : Vect k a -> List TTImp -> Res $ Vect k Name
        run [] []                        = Right []
        run (_ :: as) ((IVar _ n) :: ts) = (n ::) <$> run as ts
        run _         _                  = Left err

-- Renames all type parameter names in an argument's
-- type according to the given Vect of pairs.
-- Returns the renamed type and `True` if at least
-- one parameter was found, `False` otherwise.
private
rename : Vect n (Name,Name) -> TTImp -> (TTImp, Bool)
rename ns (IVar x n)        = case lookup n ns of
                                Nothing => (IVar x n, False)
                                Just n' => (IVar x n', True)

rename ns (IPi x y z w a r) = let (a',ba) = rename ns a
                                  (r',br) = rename ns r
                               in (IPi x y z w a' r', ba || br)

rename ns (IApp x y z)      = let (y',by) = rename ns y
                                  (z',bz) = rename ns z
                               in (IApp x y' z', by || bz)

rename _ t                  = (t, False)

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
-- names and tries to remove the corresponding implicit
-- arguments from the head of the given argument list.
-- Extracts explicit argument names and types from the rest of
-- the list.
--
-- Fails if : a) Not all values in `names` are present as implicit
--               function arguments
--            b) The function has additional non-implicit arguments
private
argPairs :  (con : Name)
         -> Vect n (Name,Name)
         -> List NamedArg
         -> Res $ List ExplicitArg
argPairs con names = run names
  where delete : Name -> Vect (S k) (Name,a) -> Res $ Vect k (Name,a)
        delete m ((n,a) :: ns)  =
          if m == n then Right ns
                    else case ns of
                              []        => implicitErr con m
                              ns@(_::_) => ((n,a) ::) <$> delete m ns

        mkArg : NamedArg -> Res ExplicitArg
        mkArg (MkArg _ ExplicitArg n t) = let (t',isP) = rename names t
                                           in Right $ MkExplicitArg n t' isP
        mkArg (MkArg _ _ n _)           = implicitErr con n

        run : Vect k (Name,a) -> List NamedArg -> Res $ List ExplicitArg
        run [] as = traverse mkArg as
        run ps@(_::_) ((MkArg _ ImplicitArg n _) :: t) = run !(delete n ps) t
        run ps _ = indicesErr con (map fst ps)


private
paramCon : Vect n Name -> Con -> Res $ ParamCon
paramCon ns (MkCon n as t) = do params <- conParams n ns t
                                args   <- argPairs n (zip params ns) as
                                pure $ MkParamCon n args

private
toParamTypeInfo : TypeInfo -> Res ParamTypeInfo
toParamTypeInfo (MkTypeInfo n as cs) =
  do ps  <- traverse expPair as
     let ns = map fst $ fromList ps
     cs' <- traverse (paramCon ns) cs
     pure $ MkParamTypeInfo n ps cs'
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
getParamInfo' : Name -> Elab ParamTypeInfo
getParamInfo' n = do ti         <- getInfo' n
                     (Right pt) <- pure (toParamTypeInfo ti)
                                | (Left err) => fail err
                     pure pt

||| macro version of `getParamInfo`.
export %macro
getParamInfo : Name -> Elab ParamTypeInfo
getParamInfo = getParamInfo'
