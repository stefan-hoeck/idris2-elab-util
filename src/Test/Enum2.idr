||| The examples in this module correspond to the REPL output shown
||| in `Doc.Enum2`. If these no longer typecheck, the corresponding
||| pretty printer must be fixed and the example in `Doc.Enum2` adjusted.
module Test.Enum2

import Language.Reflection.Syntax.Ops
import Language.Reflection.Util

ex1 : List Decl
ex1 =
  [ IClaim
      emptyFC
      MW
      Private
      []
      (mkTy
         { name = "eq"
         , type =
                 MkArg MW ExplicitArg Nothing (var "T")
             .-> MkArg MW ExplicitArg Nothing (var "T")
             .-> var "Bool"
         })
  , IDef
      emptyFC
      "eq"
      [ var "eq" .$ var "A" .$ var "A" .= var "True"
      , var "eq" .$ var "B" .$ var "B" .= var "True"
      , var "eq" .$ implicitTrue .$ implicitTrue .= var "False"
      ]
  ]

ex2 : TypeInfo
ex2 =
  MkTypeInfo
    { name = "Prelude.EqOrd.Eq"
    , arty = 1
    , args = [MkArg MW ExplicitArg (Just "ty") (hole "_")]
    , argNames = ["ty"]
    , cons =
        [ MkCon
            { name = "Prelude.EqOrd.MkEq"
            , arty = 3
            , args =
                [ MkArg M0 ImplicitArg (Just "ty") type
                , MkArg
                    MW
                    ExplicitArg
                    (Just "==")
                    (    MkArg MW ExplicitArg (Just "{arg:528}") (var "ty")
                     .-> MkArg MW ExplicitArg (Just "{arg:531}") (var "ty")
                     .-> var "Prelude.Basics.Bool")
                , MkArg
                    MW
                    ExplicitArg
                    (Just "/=")
                    (    MkArg MW ExplicitArg (Just "{arg:538}") (var "ty")
                     .-> MkArg MW ExplicitArg (Just "{arg:541}") (var "ty")
                     .-> var "Prelude.Basics.Bool")
                ]
            , typeArgs = [Regular (var "ty")]
            }
        ]
    }
