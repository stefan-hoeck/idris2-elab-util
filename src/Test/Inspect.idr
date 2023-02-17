||| The examples in this module correspond to the REPL output shown
||| in `Doc.Inspect`. If these no longer typecheck, the corresponding
||| pretty printer must be fixed and the example in `Doc.Inspect` adjusted.
module Test.Inspect

import Language.Reflection.Syntax

ex1 : TTImp
ex1 = var "*" .$ (var "fromInteger" .$ primVal (BI 2)) .$ var "x"

ex2 : TTImp
ex2 =
      MkArg MW AutoImplicit Nothing (var "Show" .$ var "a")
  .-> MkArg MW ExplicitArg (Just "val") (var "a")
  .-> primVal (PrT StringType)

ex3 : TTImp
ex3 =
  lam (MkArg MW ExplicitArg (Just "x") implicitFalse) $
  lam (MkArg MW ExplicitArg (Just "y") implicitFalse) $
  var "++" .$ var "x" .$ (var "reverse" .$ var "y")

ex4 : TTImp
ex4 =
  iCase
    { sc = var "x"
    , ty = implicitFalse
    , clauses =
        [ var "EQ" .= var "fromString" .$ primVal (Str "eq")
        , var "LT" .= var "fromString" .$ primVal (Str "lt")
        , var "GT" .= var "fromString" .$ primVal (Str "gt")
        ]
    }

ex5 : TTImp
ex5 =
  iLet
    { count = MW
    , name = "val"
    , type = implicitTrue
    , val = var "show" .$ var "x"
    , scope = var "==" .$ var "val" .$ (var "reverse" .$ var "val")
    }

ex6 : TTImp
ex6 =
  iCase
    { sc = var "x"
    , ty = var "Bool"
    , clauses = [var "True" .= var "y", var "False" .= var "z"]
    }

ex7 : TTImp
ex7 =
  var "<*>" .$ (var "<*>" .$ (var "pure" .$ var "fun") .$ var "x") .$ var "y"

ex8 : TTImp
ex8 =
     var ">>="
  .$ var "run"
  .$ (lam (MkArg MW ExplicitArg (Just "x") implicitFalse) $
      var ">>" .$ (var "action" .$ var "x") .$ (var "pure" .$ var "x"))

ex9 : TTImp
ex9 =
     var ">>="
  .$ var "xs"
  .$ (lam (MkArg MW ExplicitArg (Just "x") implicitFalse) $
       var ">>"
    .$ (var "guard" .$ (var "even" .$ var "x"))
    .$ (var "pure" .$ (var "*" .$ var "x" .$ var "x")))

ex10 : List Decl
ex10 =
  [ IClaim
      emptyFC
      MW
      Export
      [Inline]
      (MkTy
         emptyFC
         emptyFC
         "test"
         (    MkArg MW ExplicitArg Nothing (primVal (PrT IntType))
          .-> primVal (PrT IntType)))
  , IDef
      emptyFC
      "test"
      [var "test" .$ bindVar "n" .= var "+" .$ var "n" .$ var "n"]
  ]

ex11 : List Decl
ex11 =
  [ IData
      emptyFC
      Private
      Nothing
      (MkData
         emptyFC
         "Foo"
         (Just (MkArg MW ExplicitArg Nothing type .-> type))
         []
         [ MkTy
             emptyFC
             emptyFC
             "A"
             (    MkArg MW ExplicitArg Nothing (bindVar "t")
              .-> var "Foo" .$ bindVar "t")
         , MkTy emptyFC emptyFC "B" (var "Foo" .$ bindVar "t")
         ])
  ]
