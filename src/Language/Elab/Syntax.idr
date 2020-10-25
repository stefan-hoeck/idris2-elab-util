||| Some utilities for defining and manipulating TTImp values
||| for writing elaborator scripts.
|||
||| Some notes: Use quotes whenever possible:
|||
||| Names can be quoted like so: `{{ AName }}, `{{ In.Namespace.AName }}.
||| Both examples are of type Language.Reflection.TT.Name.
|||
||| Expressions can be quoted like so: `(\x => x * x)
module Language.Elab.Syntax

import Language.Reflection
import Language.Elab.Pretty
import Text.PrettyPrint.Prettyprinter

||| Creates a variable from the given name
|||
||| Names are best created using name quotes: `{{ AName }},
||| `{{ In.Namespacs.Name }}.
|||
||| Likewise, if the name is already known at the time of
||| writing, use quotes for defining a variable directly: `(AName)
export
iVar : Name -> TTImp
iVar = IVar EmptyFC

export
iBindVar : String -> TTImp
iBindVar = IBindVar EmptyFC

infixl 6 `iApp`

||| Function application.
|||
||| Example: ```iVar (UN "Just") `iApp` iVar (UN "x")```
export
iApp : TTImp -> TTImp -> TTImp
iApp = IApp EmptyFC

export
appAll : Name -> List Name -> TTImp
appAll n ns = run (iVar n) ns
  where run : TTImp -> List Name -> TTImp
        run tti []        = tti
        run tti (x :: xs) = run (tti `iApp` iVar x) xs

export
iImplicitApp : TTImp -> Maybe Name -> TTImp -> TTImp
iImplicitApp = IImplicitApp EmptyFC

export
implicitTrue : TTImp
implicitTrue = Implicit EmptyFC True

export
implicitFalse : TTImp
implicitFalse = Implicit EmptyFC False

export
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

export
iClaim : Count -> Visibility -> List FnOpt -> ITy -> Decl
iClaim = IClaim EmptyFC

export
mkTy : (n : Name) -> (ty : TTImp) -> ITy
mkTy = MkTy EmptyFC

export
listOf : List TTImp -> TTImp
listOf [] = `( Nil )
listOf (x :: xs) = `( ~(x) :: ~(listOf xs) )

export
iPi : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi = IPi EmptyFC

export
iLam : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (lamTy : TTImp) -> TTImp
iLam = ILam EmptyFC

export
iLet : Count -> Name -> (nTy : TTImp) -> (nVal : TTImp)
    -> (scope : TTImp) -> TTImp
iLet = ILet EmptyFC

export
iCase : TTImp -> (ty : TTImp)
     -> List Clause -> TTImp
iCase = ICase EmptyFC

export
iDef : Name -> List Clause -> Decl
iDef = IDef EmptyFC

export
iAs : Name -> TTImp -> TTImp
iAs = IAs EmptyFC UseLeft  

export
iPrimVal : (c : Constant) -> TTImp
iPrimVal = IPrimVal EmptyFC

export
iType :  TTImp
iType = IType EmptyFC

private errMsg : Name -> List (Name,TTImp) -> String
errMsg n [] = show n ++ " is not in scope."
errMsg n xs = let rest = concat $ intersperse ", " $ map (show . fst) xs
               in show n ++ " is not unique: " ++ rest

export
adjustNS : Name -> Elab Name
adjustNS n@(UN _) = inCurrentNS n
adjustNS n        = pure n

||| Looks up a name in the current namespace.
export
lookupName : Name -> Elab (Name, TTImp)
lookupName n' = do
  n            <- adjustNS n'
  [(name,imp)] <- getType n | xs => fail $ errMsg n' xs
  pure (name,imp)

export
getExplicitArgs : Name -> Elab (List Name)
getExplicitArgs n = lookupName n >>= (run . snd)
  where
    run : TTImp -> Elab (List Name)
    run (IPi _ _ ExplicitArg _ _ retTy) = [| genSym "arg" :: run retTy |]
    run (IPi _ _ _ _ _ retTy)           = run retTy -- skip implicit args
    run _                               = pure []

export
printLocalVars : Elab ()
printLocalVars = do vs <- localVars
                    logMsg "Local vars: " 10 (show vs)