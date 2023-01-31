||| The examples in this module correspond to the REPL output shown
||| in `Doc.Generic2`. If these no longer typecheck, the corresponding
||| pretty printer must be fixed and the example in `Doc.Generic2` adjusted.
module Test.Generic2

import Language.Reflection.Syntax
import Language.Reflection.Types

ex1 : TypeInfo
ex1 =
  MkTypeInfo
    { name = "Prelude.Types.Maybe"
    , arty = 1
    , args = [MkArg MW ExplicitArg (Just "ty") type]
    , argNames = ["ty"]
    , cons =
        [ MkCon
            { name = "Prelude.Types.Nothing"
            , arty = 1
            , args = [MkArg M0 ImplicitArg (Just "ty") type]
            , typeArgs = [Regular (var "ty")]
            }
        , MkCon
            { name = "Prelude.Types.Just"
            , arty = 2
            , args =
                [ MkArg M0 ImplicitArg (Just "ty") type
                , MkArg MW ExplicitArg (Just "x") (var "ty")
                ]
            , typeArgs = [Regular (var "ty")]
            }
        ]
    }

ex2 : TypeInfo
ex2 =
  MkTypeInfo
    { name = "Prelude.Types.Either"
    , arty = 2
    , args =
        [ MkArg MW ExplicitArg (Just "a") type
        , MkArg MW ExplicitArg (Just "b") type
        ]
    , argNames = ["a", "b"]
    , cons =
        [ MkCon
            { name = "Prelude.Types.Left"
            , arty = 3
            , args =
                [ MkArg M0 ImplicitArg (Just "a") type
                , MkArg M0 ImplicitArg (Just "b") type
                , MkArg MW ExplicitArg (Just "x") (var "a")
                ]
            , typeArgs = [Regular (var "a"), Regular (var "b")]
            }
        , MkCon
            { name = "Prelude.Types.Right"
            , arty = 3
            , args =
                [ MkArg M0 ImplicitArg (Just "a") type
                , MkArg M0 ImplicitArg (Just "b") type
                , MkArg MW ExplicitArg (Just "x") (var "b")
                ]
            , typeArgs = [Regular (var "a"), Regular (var "b")]
            }
        ]
    }

ex3 : TypeInfo
ex3 =
  MkTypeInfo
    { name = "Data.Vect.Vect"
    , arty = 2
    , args =
        [ MkArg MW ExplicitArg (Just "len") (var "Prelude.Types.Nat")
        , MkArg MW ExplicitArg (Just "elem") type
        ]
    , argNames = ["len", "elem"]
    , cons =
        [ MkCon
            { name = "Data.Vect.Nil"
            , arty = 1
            , args = [MkArg M0 ImplicitArg (Just "elem") type]
            , typeArgs = [Regular (var "Prelude.Types.Z"), Regular (var "elem")]
            }
        , MkCon
            { name = "Data.Vect.(::)"
            , arty = 4
            , args =
                [ MkArg M0 ImplicitArg (Just "len") (var "Prelude.Types.Nat")
                , MkArg M0 ImplicitArg (Just "elem") type
                , MkArg MW ExplicitArg (Just "x") (var "elem")
                , MkArg
                    MW
                    ExplicitArg
                    (Just "xs")
                    (var "Data.Vect.Vect" .$ var "len" .$ var "elem")
                ]
            , typeArgs =
                [ Regular (var "Prelude.Types.S" .$ var "len")
                , Regular (var "elem")
                ]
            }
        ]
    }

ex4 : TypeInfo
ex4 =
  MkTypeInfo
    { name = "Doc.Generic2.ASum"
    , arty = 2
    , args =
        [ MkArg MW ExplicitArg (Just "a") type
        , MkArg MW ExplicitArg (Just "b") type
        ]
    , argNames = ["a", "b"]
    , cons =
        [ MkCon
            { name = "Doc.Generic2.L"
            , arty = 3
            , args =
                [ MkArg M0 ImplicitArg (Just "y") type
                , MkArg M0 ImplicitArg (Just "x") type
                , MkArg MW ExplicitArg (Just "{arg:8392}") (var "x")
                ]
            , typeArgs = [Regular (var "x"), Regular (var "y")]
            }
        , MkCon
            { name = "Doc.Generic2.R"
            , arty = 3
            , args =
                [ MkArg M0 ImplicitArg (Just "s") type
                , MkArg M0 ImplicitArg (Just "t") type
                , MkArg
                    MW
                    ExplicitArg
                    (Just "{arg:8397}")
                    (var "Prelude.Types.Maybe" .$ var "t")
                ]
            , typeArgs = [Regular (var "s"), Regular (var "t")]
            }
        ]
    }
