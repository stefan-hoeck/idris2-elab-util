module Language.Elab.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import Language.Elab.Pretty
import Language.Elab.Syntax
import Language.Reflection
import Text.PrettyPrint.Prettyprinter

public export
record ArgInfo where
  constructor MkArgInfo
  index   : Nat
  count   : Count
  piInfo  : PiInfo TTImp
  name    : Name
  type    : TTImp

isExplicit : ArgInfo -> Bool
isExplicit (MkArgInfo _ _ ExplicitArg _ _) = True
isExplicit (MkArgInfo _ _ _           _ _) = False

export
Pretty ArgInfo where
  pretty (MkArgInfo index count piInfo name type) =
    parens $ hsepH [index, count, piInfo, name, ":", type]

public export
record Constructor where
  constructor MkConstructor
  name : Name
  args : List ArgInfo
  type : TTImp

export
zipWithIndex : List a -> List (Nat,a)
zipWithIndex = run 0
  where run : Nat -> List a -> List (Nat,a)
        run k []        = []
        run k (x :: xs) = (k,x) :: run (S k) xs

export
mkExplicitArgNames : List ArgInfo -> List Name
mkExplicitArgNames = map argName . filter isExplicit
  where argName : ArgInfo -> Name
        argName arg = UN $ "x" ++ show (index arg)

export
appConstructor : Constructor -> TTImp
appConstructor (MkConstructor n args _) =
  appAll n (mkExplicitArgNames args)

export
calcArgs : TTImp -> Elab (List ArgInfo, TTImp)
calcArgs = run 0
  where run : Nat -> TTImp -> Elab (List ArgInfo, TTImp)
        run k (IPi _ c pi n t retTy) =
          do (args,tpe) <- run (S k) retTy
             Just n'    <- pure n | Nothing => fail "unnamed pi"
             pure (MkArgInfo k c pi n' t :: args,tpe)
        run _ tpe = pure ([],tpe)

export
getCon : Name -> Elab Constructor
getCon n = do (n',tt)    <- lookupName n
              (args,tpe) <- calcArgs tt
              pure $ MkConstructor n' args tpe

export
getArgs : Name -> Elab (List ArgInfo)
getArgs = map args . getCon

export
Pretty Constructor where
  pretty (MkConstructor n args tpe) = pretty n <++> prettyFun args tpe

public export
record TypeInfo where
  constructor MkTypeInfo
  name : Name
  args : List ArgInfo
  cons : List Constructor
  type : TTImp

export
getInfo : Name -> Elab TypeInfo
getInfo n = 
  do (n',tt)    <- lookupName n
     (args,tpe) <- calcArgs tt
     conNames   <- getCons(n')
     cons       <- traverse getCon conNames
     pure (MkTypeInfo n' args cons tpe)

export
Pretty TypeInfo where
  pretty (MkTypeInfo name args cons type) =
    let head = pretty name <++> prettyFun args (IType EmptyFC)
        cons = indent 2 $ vsep (map pretty cons)
     in vsep [head,cons]
