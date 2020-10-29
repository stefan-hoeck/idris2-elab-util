module Language.Reflection.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection
import Text.PrettyPrint.Prettyprinter

public export
record Arg where
  constructor MkArg
  index   : Nat
  count   : Count
  piInfo  : PiInfo TTImp
  name    : Name
  type    : TTImp

export
isExplicit : Arg -> Bool
isExplicit (MkArg _ _ ExplicitArg _ _) = True
isExplicit (MkArg _ _ _           _ _) = False

export
Pretty Arg where
  pretty (MkArg _ count piInfo name type) =
    parens $ hsepH [count, piInfo, name, ":", type]

public export
record Con where
  constructor MkCon
  name : Name
  args : List Arg
  type : TTImp

export
zipWithIndex : List a -> List (Nat,a)
zipWithIndex = run 0
  where run : Nat -> List a -> List (Nat,a)
        run k []        = []
        run k (x :: xs) = (k,x) :: run (S k) xs

export
explicitArgNames : List Arg -> List Name
explicitArgNames = map argName . filter isExplicit
  where argName : Arg -> Name
        argName arg = UN $ "x" ++ show (index arg)

export
appExplicitArgs : Name -> List Arg -> TTImp
appExplicitArgs n args = appAll n (explicitArgNames args)

export
calcArgs : TTImp -> Elab (List Arg, TTImp)
calcArgs = run 0
  where run : Nat -> TTImp -> Elab (List Arg, TTImp)
        run k (IPi _ c pi n t retTy) =
          do (args,tpe) <- run (S k) retTy
             Just n'    <- pure n | Nothing => fail "unnamed pi"
             pure (MkArg k c pi n' t :: args,tpe)
        run _ tpe = pure ([],tpe)

export
getCon : Name -> Elab Con
getCon n = do (n',tt)    <- lookupName n
              (args,tpe) <- calcArgs tt
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

export %macro
getInfo : Name -> Elab TypeInfo
getInfo n = 
  do (n',tt)    <- lookupName n
     (args,tpe) <- calcArgs tt
     conNames   <- getCons n'
     cons       <- traverse getCon conNames
     pure (MkTypeInfo n' args cons tpe)

export
Pretty TypeInfo where
  pretty (MkTypeInfo name args cons type) =
    let head = applyH Open "MkTypeInfo" [name, args, type]
        cons = indent 2 $ vsep (map pretty cons)
     in vsep [head,cons]
