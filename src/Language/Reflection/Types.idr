module Language.Reflection.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection
import Text.PrettyPrint.Prettyprinter

%language ElabReflection

public export
record Con where
  constructor MkCon
  name : Name
  args : List Arg
  type : TTImp

export
getCon : Name -> Elab Con
getCon n = do (n',tt)    <- lookupName n
              let (args,tpe) = unPi tt
              pure $ MkCon n' args tpe

export
Pretty Con where
  prettyPrec p (MkCon n args tpe) = applyH p "MkCon" [n, args, tpe]

public export
record TypeInfo where
  constructor MkTypeInfo
  name : Name
  args : List Arg
  cons : List Con
  type : TTImp

export
getInfo' : Name -> Elab TypeInfo
getInfo' n = 
  do (n',tt)    <- lookupName n
     let (args,tpe) = unPi tt
     conNames   <- getCons n'
     cons       <- traverse getCon conNames
     pure (MkTypeInfo n' args cons tpe)

export %macro
getInfo : Name -> Elab TypeInfo
getInfo = getInfo'

export
Pretty TypeInfo where
  pretty (MkTypeInfo name args cons type) =
    let head = applyH Open "MkTypeInfo" [name, args, type]
        cons = indent 2 $ vsep (map pretty cons)
     in vsep [head,cons]

export %macro
singleCon : Name -> Elab Name
singleCon n = do (MkTypeInfo _ _ cs _) <- getInfo' n
                 (c::Nil) <- pure cs | _ => fail "not a single constructor"
                 pure $ name c

--------------------------------------------------------------------------------
--          Parameterized Types
--------------------------------------------------------------------------------

public export
Res : Type -> Type
Res = Either String

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

public export
record ParamCon where
  constructor MkParamCon
  name         : Name
  explicitArgs : List ExplicitArg

export
Pretty ParamCon where
  prettyPrec p (MkParamCon n explicitArgs) =
    applyH p "MkParamCon" [n, explicitArgs]

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

Eq Namespace where
  (MkNS xs) == (MkNS ys) = xs == ys

Eq Name where
  (UN a)   == (UN x)   = a == x
  (MN a b) == (MN x y) = a == x && b == y
  (NS a b) == (NS x y) = a == x && b == y
  (DN a b) == (DN x y) = a == x && b == y
  (RF a)   == (RF x)   = a == x
  _        == _        = False

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

private
defName : Int -> Maybe Name -> Name
defName k = fromMaybe (UN $ "x" ++ show k)

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
         -> List Arg
         -> Res $ List ExplicitArg
argPairs con names = run names
  where notParamErr : Maybe Name -> String
        notParamErr n = show con
                      ++ ": Non-explicit argument "
                      ++ maybe "_" show n
                      ++ " is not a type parameter."

        indicesErr : Vect k (Name,a) -> String
        indicesErr v = show con ++ ": Type indices found: " ++ show (map fst v)

        rename : TTImp -> (TTImp, Bool)
        rename (IVar x n)        = case lookup n names of
                                        Nothing => (IVar x n, False)
                                        Just n' => (IVar x n', True)

        rename (IPi x y z w a r) = let (a',ba) = rename a
                                       (r',br) = rename r
                                    in (IPi x y z w a' r', ba || br)

        rename (IApp x y z)      = let (y',by) = rename y
                                       (z',bz) = rename z
                                    in (IApp x y' z', by || bz)

        rename t                 = (t, False)

        delete : Maybe Name -> Vect (S k) (Name,a) -> Res $ Vect k (Name,a)
        delete m ((n,a) :: ns)  =
          if m == Just n then Right ns
                         else case ns of
                                   [] => Left $ notParamErr m
                                   ns@(_ :: _) => ((n,a) ::) <$> delete m ns

        mkArg : (Int,Arg) -> Res ExplicitArg
        mkArg (k,MkArg _ ExplicitArg n t) = let (t',isP) = rename t
                                                n'       = defName k n
                                             in Right $ MkExplicitArg n' t' isP
        mkArg (_,MkArg _ _ n _)           = Left $ notParamErr n

        run : Vect k (Name,a) -> List Arg -> Res $ List ExplicitArg
        run [] as = traverse mkArg $ zipWithIndex as
        run ps@(_ :: _) ((MkArg _ ImplicitArg n _) :: as) =
          delete n ps >>= (\ps' => run ps' as)
        run ps _ = Left $ indicesErr ps


private
paramCon : Vect n Name -> Con -> Res $ ParamCon
paramCon ns (MkCon n as t) = do params <- conParams n ns t
                                args   <- argPairs n (zip params ns) as
                                pure $ MkParamCon n args

export
toParamTypeInfo : TypeInfo -> Res ParamTypeInfo
toParamTypeInfo (MkTypeInfo n as cs t) =
  do ps  <- expPairs 0 as
     let ns = map fst $ fromList ps
     cs' <- traverse (paramCon ns) cs
     pure $ MkParamTypeInfo n ps cs'
  where err : String
        err = show n ++ ": Non-explicit type arguments are not supported"

        expPairs : Int -> List Arg -> Res $ List (Name,TTImp)
        expPairs _ [] = Right []
        expPairs k ((MkArg _ ExplicitArg n t) :: xs) =
          ((defName k n,t) ::) <$> expPairs (k+1) xs
        expPairs _ ((MkArg _ _ _ _) :: _) = Left err

export
getParamInfo' : Name -> Elab ParamTypeInfo
getParamInfo' n = do ti         <- getInfo' n
                     (Right pt) <- pure (toParamTypeInfo ti)
                                | (Left err) => fail err
                     pure pt

export %macro
getParamInfo : Name -> Elab ParamTypeInfo
getParamInfo = getParamInfo'
