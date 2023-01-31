||| The examples in this module correspond to the REPL output shown
||| in `Doc.Enum1`. If these no longer typecheck, the corresponding
||| pretty printer must be fixed and the example in `Doc.Enum1` adjusted.
module Test.Enum1

import Language.Reflection.Syntax

ex1 : List Decl
ex1 =
  [ IData
      emptyFC
      Private
      Nothing
      (MkData
         emptyFC
         "Enum"
         (Just type)
         []
         [ mkTy {name = "A", type = var "Enum"}
         , mkTy {name = "B", type = var "Enum"}
         , mkTy {name = "C", type = var "Enum"}
         ])
  ]
