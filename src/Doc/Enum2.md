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
      enum         = arg $ varStr enumName

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
of public toplevel functions. Finally, `(.=)` is an infix
operator for defining pattern clauses.


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
the implementation of an interface directly. The following
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
inspectEq (Eq at Prelude/EqOrd.idr:13:1--22:7 _ _) = ?eqTest_rhs_1
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
constructor of `Eq`, define local implementations for
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
      mkEq         = singleCon "Prelude.Eq"
      eqName       = UN "eq"
      functionName = UN $ "implEq" ++ enumName

      -- vars
      eq           = var eqName
      function     = var functionName
      enum         = arg $ varStr enumName

      -- Catch all case: eq _ _ = False
      defEq = eq .$ implicitTrue .$ implicitTrue .= `(False)

      -- single pattern clause: `eq X X = True`
      mkC   = \x => eq .$ varStr x .$ varStr x .= `(True)

      -- implementation of (/=)
      neq = `(\a,b => not $ eq a b)

      -- local where block:
      -- ... = EqConstructor eq neq
      --   where eq : Enum -> Enum -> Bool
      --         eq A A = True
      --         ...
      --         eq _ _ = False
      impl  = local [ private' eqName $ enum .-> enum .-> `(Bool)
                    , def eqName $ map mkC cons ++ [defEq] 
                    ] (var mkEq .$ eq .$ neq)

   in [ interfaceHint Public functionName (var "Eq" .$ type enum)
      , def functionName [ function .= impl ] ]
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

eqTest3 : (Male /= NonBinary) = True
eqTest3 = Refl
```

Neat.

In our implementation, we define a local function `eq`
in a `where` block and pass it to `Eq`s constructor,
together with its complement `neq`, which was
defined cleanly via a quoted lambda.

### Other Interfaces

Nothing stops us from implementing additional
interfaces. For completeness, we provide implementations
of `Show` and `Ord` below.

```idris
export
ordImpl : String -> List String -> List Decl
ordImpl enumName cons =
  let -- names
      mkOrd        = singleCon "Prelude.Ord"
      compName     = UN "comp"
      functionName = UN $ "implOrd" ++ enumName

      -- vars
      eq           = varStr $ "implEq" ++ enumName
      comp         = var compName
      function     = var functionName
      enum         = arg $ varStr enumName

      -- single pattern clauses: `comp X X = EQ`
      --                         `comp X _ = LT`
      --                         `comp _ X = GT`
      mkC   = \x => [ comp .$ varStr x .$ varStr x     .= `(EQ)
                    , comp .$ varStr x .$ implicitTrue .= `(LT) 
                    , comp .$ implicitTrue .$ varStr x .= `(GT) 
                    ]

      -- implementations of (>),(>=),(<),(<=),min,max
      lt  = `(\a,b => comp a b == LT)
      gt  = `(\a,b => comp a b == GT)
      leq = `(\a,b => comp a b /= GT)
      geq = `(\a,b => comp a b /= LT)
      max = `(\a,b => if comp a b == GT then a else b)
      min = `(\a,b => if comp a b == LT then a else b)

      impl = local [ private' compName $ enum .-> enum .-> `(Ordering)
                   , def compName $ cons >>= mkC
                   ] (var mkOrd .$ eq .$ comp .$ lt .$ gt .$ leq .$ geq .$ max .$ min)

   in [ interfaceHint Public functionName (var "Ord" .$ type enum)
      , def functionName [ function .= impl ] ]
```

The only true hurdle when writing the code above was the realization
that the `Eq` instance had to be passed explicitly as an argument
to the `Ord` constructor.

```idris
export
showImpl : String -> List String -> List Decl
showImpl enumName cons =
  let -- names
      mkShow       = singleCon "Prelude.Show"
      showName     = UN "show"
      functionName = UN $ "implShow" ++ enumName

      -- vars
      show         = var showName
      function     = var functionName
      enum         = arg $ varStr enumName

      -- single pattern clause: `show X = "X"`
      mkC   = \x => show .$ varStr x .= primVal (Str x)

      showPrec  = `(\_,v => show v)

      impl = local [ private' showName $ enum .-> `(String)
                   , def showName $ map mkC cons
                   ] (var mkShow .$ show .$ showPrec)

   in [ interfaceHint Public functionName (var "Show" .$ type enum)
      , def functionName [ function .= impl ] ]
```

We can now define a macro for automatically creating
enums plus corresponding interface implementations:

```idris
mkEnumTc : String -> List String -> Elab ()
mkEnumTc n cons = declare $  enumDecl n cons
                          :: eqImpl   n cons
                          ++ ordImpl  n cons
                          ++ showImpl n cons
```

Let's use this to define `Weekday` and run some tests.

```idris
%runElab (mkEnumTc "Weekday" [ "Monday"
                             , "Tuesday"
                             , "Wednesday"
                             , "Thursday"
                             , "Friday"
                             , "Saturday"
                             , "Sunday"])


weekdayTest1 : Monday == Monday = True
weekdayTest1 = Refl

weekdayTest2 : Sunday == Friday = False
weekdayTest2 = Refl

weekdayTest3 : Sunday > Friday = True
weekdayTest3 = Refl

weekdayTest4 : Monday >= Wednesday = False
weekdayTest4 = Refl

weekdayTest5 : show Thursday = "Thursday"
weekdayTest5 = Refl
```

### What's next

Now that we got a first taste of automatic interface derivation, wouldn't
it be nice, if we could not only do this for enums but for
any feasible data type? In the [next section](Generic1.md) we look into a generic
representations for algebraic data types.
