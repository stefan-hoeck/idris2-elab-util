module Example.Language.Elab.Enum

import public Language.Elab.Pretty
import public Language.Elab.Syntax
import public Language.Elab.Types

%language ElabReflection

implClaim : (name : String) -> (tc : String) -> Decl
implClaim name tc =
  let fun = UN ("impl" ++ name ++ tc)
   in iClaim MW Public [Hint True] (mkTy fun $ iVarStr tc `iApp` iVarStr name)

export
eqImpl : (n : TTImp) -> (vals : List Name) -> List Decl
eqImpl n vals =   [ claim, iDef eq (map clause vals ++ [catch]) ]
              ++ `[ neq : ~(n) -> ~(n) -> Bool
                    neq a b = not (eq a b) ]

  where eq : Name
        eq = UN "eq"

        claim : Decl
        claim = iClaim MW Private [] (mkTy eq (n ==> n ==> `(Bool)))

        clause : Name -> Clause
        clause n = patClause (iVar eq `iApp` iVar n `iApp` iVar n) `(True)

        catch : Clause
        catch = patClause (iVar eq `iApp` implicitTrue `iApp` implicitTrue)
                         `(False)

export
test : List Decl
test = `[ test : A -> B
          test = impl
            where impl : A -> B
                  impl a = "Foo" ]
              

export
enumDecl : (name : String) -> (vals : List Name) -> Decl
enumDecl name vals = let name'   = UN name
                         nameVar = iVar name'
                         cons    = map (`mkTy` nameVar) vals
                         data'   = MkData EmptyFC name' iType [] cons
                      in IData EmptyFC Public data'

export
mkEnum : (name : String) -> (vals : List String) -> Elab ()
mkEnum name vals = declare [enumDecl name (map UN vals)]

export
eqInfo : TypeInfo
eqInfo = getInfo `{{ Prelude.EqOrd.Eq }}


--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

%runElab mkEnum "Weekday"
                (map (++ "day") ["Mon","Tues","Wednes","Thurs","Fri","Satur","Sun"])

%runElab mkEnum "Gender" ["Female","Male"]

