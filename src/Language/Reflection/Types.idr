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
record ParamCon where
  constructor MkParamCon
  name         : Name
  explicitArgs : List Arg
  type         : TTImp

export
Pretty ParamCon where
  prettyPrec p (MkParamCon n args tpe) = applyH p "MkParamCon" [n, args, tpe]

public export
record ParamTypeInfo where
  constructor MkParamTypeInfo
  name : Name
  args : List (Name,TTImp)
  cons : List ParamCon
  type : TTImp

export
Pretty ParamTypeInfo where
  pretty (MkParamTypeInfo name args cons type) =
    let head = applyH Open "MkParamTypeInfo" [name, args, type]
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

private
argPairs : List Arg -> List (Name,TTImp)
argPairs = map toPair . zipWithIndex
  where toPair : (Int,Arg) -> (Name,TTImp)
        toPair (x, (MkArg _ _ Nothing  t)) = (UN $ "a" ++ show x,t)
        toPair (_, (MkArg _ _ (Just n) t)) = (n,t)

private
rename : List (Name,Name)  -> TTImp -> TTImp
rename ns (IVar x n)        = IVar x $ fromMaybe n (lookup n ns)
rename ns (IPi x y z w a r) = IPi x y z w (rename ns a) (rename ns r)
rename ns (IApp x y z)      = IApp x (rename ns y) (rename ns z)
rename _  t                 = t

private
renameList : List Name -> TTImp -> Maybe (List (Name,Name))
renameList ns t = run ns (snd $ unApp t)
  where run : List Name -> List TTImp -> Maybe (List (Name,Name))
        run [] []                         = Just []
        run (n :: ns) ((IVar _ n') :: ts) = ((n',n) ::) <$> run ns ts
        run _         _                   = Nothing

private
paramCon : List Name -> Con -> Maybe (ParamCon)
paramCon ns (MkCon n as t) =
    map (\ps => MkParamCon n (args' ps as) (rename ps t)) (renameList ns t)
  where args' : List (Name,Name) -> List Arg -> List Arg
        args' _ [] = []
        args' ps ((MkArg c ExplicitArg n t) :: as) =
          MkArg c ExplicitArg n (rename ps t) :: args' ps as

        args' ps (_ :: as) = args' ps as

export
toParamTypeInfo : TypeInfo -> Maybe ParamTypeInfo
toParamTypeInfo (MkTypeInfo n as cs t) =
  let ps = argPairs as
      ns = map fst ps
   in map (\cs' => MkParamTypeInfo n ps cs' t) $ traverse (paramCon ns) cs

export
getParamInfo' : Name -> Elab ParamTypeInfo
getParamInfo' n = do ti        <- getInfo' n
                     (Just pt) <- pure (toParamTypeInfo ti)
                               | Nothing => fail "not a parameterized type"
                     pure pt

export %macro
getParamInfo : Name -> Elab ParamTypeInfo
getParamInfo = getParamInfo'
