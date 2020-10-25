module Language.Elab.Syntax

import Language.Reflection
import Language.Elab.Pretty
import Text.PrettyPrint.Prettyprinter

import Data.Strings -- strM

-- Some notes
--
-- IPi describes a type declaration
--  for instance : Bool -> Bool -> Bool
--    IPi _ MW ExplicitArg Nothing B (
--      IPi _ MW ExplicitArg Nothing B B
--    )
-- where B is a placeholder for "iVarStr Bool"

private
z : (Int,Int)
z = (0,0)

export
namedFC : String -> FC
namedFC s = MkFC s z z

export
iVar : Name -> TTImp
iVar = IVar EmptyFC

export
iVarStr : String -> TTImp
iVarStr = iVar . UN

export
iVarNS : List String -> String -> TTImp
iVarNS ns n = iVar (NS (MkNS ns) $ UN n)

export
iVar' : String -> Name -> TTImp
iVar' s = IVar (namedFC s)

export
iBindVar : String -> TTImp
iBindVar = IBindVar EmptyFC

export
iBindVar' : String -> String -> TTImp
iBindVar' s = IBindVar (namedFC s)

-- export
infixl 6 `iApp`
export
iApp : TTImp -> TTImp -> TTImp
iApp = IApp EmptyFC

export
iApp' : String -> TTImp -> TTImp -> TTImp
iApp' s = IApp (namedFC s)

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
implicit' : TTImp
implicit' = Implicit EmptyFC True

export
implicit'' : TTImp
implicit'' = Implicit EmptyFC False

export
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

export
patClause' : String -> (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause' s = PatClause (namedFC s)

export
iClaim : Count -> Visibility -> List FnOpt -> ITy -> Decl
iClaim = IClaim EmptyFC

export
iClaim' : String -> Count -> Visibility -> List FnOpt -> ITy -> Decl
iClaim' s = IClaim (namedFC s)

export
mkTy : (n : Name) -> (ty : TTImp) -> ITy
mkTy = MkTy EmptyFC

export
mkTy' : String -> (n : Name) -> (ty : TTImp) -> ITy
mkTy' s = MkTy (namedFC s)

export
iPi : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi = IPi EmptyFC

export
iPi' : String -> Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (retTy : TTImp) -> TTImp
iPi' s = IPi (namedFC s)

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

export
iPrimVal' : String -> (c : Constant) -> TTImp
iPrimVal' s = IPrimVal (namedFC s)

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
