## Eq Instance for Enumerations

First, again, some module setup stuff.

```idris
module Doc.Enum2

import Doc.Enum1
import Language.Reflection
import Language.Reflection.Syntax
import public Language.Reflection.Types

%language ElabReflection
```

In this section we try to automatically define `Eq` instances
for enumerations. This will be quite a bit more involved
than generating the data types themselves, so we will break
it down into several parts.

### Toplevel Equality Functions

We skip the interface part for now and focus on
implementing corresponding toplevel functions instead.
Again, we will first make use of our pretty printers to
inspect the structure of the function we want to implement:

```
...> :exec putPretty `[eq : T -> T -> Bool; eq A A = True; eq B B = True; eq _ _ = False]


  [ IClaim MW
           Private
           []
           (MkTy eq
                 (IPi.  (MW ExplicitArg : IVar T)
                     -> (MW ExplicitArg : IVar T)
                     -> IVar Bool))
  , IDef eq
         [ PatClause (IApp. IVar eq $ IVar A $ IVar A) (IVar True)
         , PatClause (IApp. IVar eq $ IVar B $ IVar B) (IVar True)
         , PatClause (IApp. IVar eq $ Implicit True $ Implicit True)
                     (IVar False) ] ]

```

So, a top-level function consists of two parts:
The function's type (wrapped in `IClaim`) and its implementation
(wrapped in `IDef`). Again, we make use of some convenience
functions (and infix operators) provided by
`Language.Reflection.Syntax`.

```idris
export
eqDecl1 : String -> List String -> List Decl
eqDecl1 enumName cons =
  let functionName = UN $ "impl1Eq" ++ enumName
      function     = var functionName
      enum         = varStr enumName

      -- Default clause for non-matching constructors:
      -- `function _ _ = False`
      defClause    = function .$ implicitTrue .$ implicitTrue .= `(False)

      -- Pattern clause for a single constructor:
      -- `function A A = True`
      conClause    = \c => function .$ varStr c .$ varStr c .= `(True)

   in [ public' functionName $ enum .-> enum .-> `(Bool)
      , def functionName $ map conClause cons ++ [defClause] ]
```

We make use of several new syntactic utilities from
`Language.Reflection.Syntax`. `(.$)` is an infix operator for
function application (`Language.Reflection.Syntax.app`),
`.->` is used to declare function types. Both are chosen
to look similar to the corresponding Idris keywords `$` and `->`.
Underscores in pattern matches can be represented by `implicitTrue`
(see also the prettified output of quoted declarations above),
and `public'` is a convenient shortcut for type declarations
of public toplevel functions.


```idris
export
mkEq1 : String -> List String -> Elab ()
mkEq1 n cons = declare $ eqDecl1 n cons

%runElab (mkEq1 "Gender" ["Female","Male","NonBinary"])

eqTest : impl1EqGender Female Female = True
eqTest = Refl
```

Great, everything seems to work as expected.

### Interface Implementation, Part 1

Unfortunately, it seems not to be possible to emulate
the definition of an interface directly. The following
quote results in an error message from Idris
(*Can't reflect a pragma*).

```
eqInterfaceDecl : List Decl
eqInterfaceDecl = `[ Eq Gender ]
```

From the [implementation notes](https://idris2.readthedocs.io/en/latest/implementation/overview.html#auto-implicits)
we learn that interfaces are translated to records and
implementations to search hints, so we might try to create
such a record value manually. However, there comes a new hurdle.
What's the name of `Eq`'s constructor? There are several ways
to find out, but easiest is probably case expansion
in interactive edting. The result comes as a surprise:

```
inspectEq : Eq Gender -> Eq Gender
inspectEq ("Eq at Prelude/EqOrd.idr:13:1--22:7" = /=) = ?eqTest_rhs_1
```

This does not seem to be a constructor we can use
in a quote directly. However, it is possible to reflect on it and
use it in metaprograms. `Language.Reflection` defines utilities
for finding data types and their constructors by name.
In addition, module `Language.Reflect.Types` in this package
allows us to gather detailed information about data types.

```idris
export
eqInfo : TypeInfo
eqInfo = getInfo "Prelude.Eq"
```

Pretty printing the above `TypeInfo` yields the following:

```
Doc.Enum2> :exec putPretty eqInfo

  MkTypeInfo Prelude.EqOrd.Eq [(MW ExplicitArg ty : IHole _)] IType
    MkCon Prelude.EqOrd.Eq at Prelude/EqOrd.idr:13:1--22:7
          [ (M0 ImplicitArg ty : IType)
          , (MW ExplicitArg == : IPi.  (MW ExplicitArg {arg:2} : IVar ty)
                                    -> (MW ExplicitArg {arg:3} : IVar ty)
                                    -> IVar Prelude.Basics.Bool)
          , (MW ExplicitArg /= : IPi.  (MW ExplicitArg {arg:4} : IVar ty)
                                    -> (MW ExplicitArg {arg:5} : IVar ty)
                                    -> IVar Prelude.Basics.Bool) ]
          (IApp. IVar Prelude.EqOrd.Eq $ IVar ty)

```

### Interface Implementation, Part 2

The above output shows the general structure we are heading towards.
We somehow need to get access to that horribly named
constructor of `Eq`, define two local implementations for
`(==)` and `(/=)` and then apply those implementations
to the constructor.

Luckily, module `Language.Reflection.Types` provides a macro `singleCon`
for extracting the name of the sole constructor of a data type
if it exists. Otherwise the elaborator fails, throwing a compile-time
exception.

```idris
export
eqImpl : String -> List String -> List Decl
eqImpl enumName cons =
  let -- names
      eq    = UN "eq"
      neq   = UN "neq"
      fun   = UN $ "implEq" ++ enumName
      eqCon = singleCon "Prelude.Eq"

      -- vars
      eqV   = var eq
      neqV  = var neq
      funV  = var fun
      enumV = varStr enumName

      -- Type of eq and neq : EnumName -> EnumName -> Bool
      eqTpe = enumV .-> enumV .-> `(Bool)

      -- Catch all case: eq _ _ = False
      defEq = eqV .$ implicitTrue .$ implicitTrue .= `(False)

      -- single pattern clause: `eq X X = True`
      mkC   = \x => eqV .$ x .$ x .= `(True)

      -- local where block:
      -- ... = EqConstructor eq neq
      --   where eq : EnumName -> EnumName -> Bool
      --         eq A A = True
      --         eq B B = True
      --         eq _ _ = False
      --
      --         neq : EnumName -> EnumName -> Bool
      --         neq a b = not (eq a b)
      impl  = local [ private' eq eqTpe
                    , def eq $ map (mkC . varStr) cons ++ [defEq] 

                    , private' neq eqTpe
                    , def neq [`(neq a b) .= `(not (eq a b))]
                    ] (var eqCon .$ eqV .$ neqV)

   in [ interfaceHint Public fun (var "Eq" .$ enumV)
      , def fun [ patClause funV impl ] ]
```

We will break this down in a moment. First, we check whether
it actually works:

```
export
mkEqImpl : String -> List String -> Elab ()
mkEqImpl enumName cons = declare (eqImpl enumName cons)

%runElab (mkEqImpl "Gender" ["Female","Male","NonBinary"])

eqTest2 : (Male == NonBinary) = False
eqTest2 = Refl
```

Neat.
