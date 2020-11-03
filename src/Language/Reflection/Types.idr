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
