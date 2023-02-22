# Inspecting the Structure of Idris Expressions

```idris
module Doc.Inspect

import Data.List1
import Language.Reflection
import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops
```

In this section of the tutorial, we will learn how
to look at the underlying structure of Idris expressions.
Most of the examples can be run from the REPL.

To better visualize the sometimes deeply nested
syntax trees, [pretty printers](../Language/Reflection/Pretty.idr)
are provided for all public
data types in modules `Language.Reflection.TT` and
`Language.Reflection.TTImp`.

Before we begin, make sure you have the [prettier](https://github.com/Z-snails/prettier)
package installed, either by using the [pack](https://github.com/stefan-hoeck/idris2-pack)
package manager (the recommended way), or by running `make deps`.

Since the Idris REPL does not yet support scrolling
through its command history, I suggest using the
command-line utility [rlwrap](https://github.com/hanslub42/rlwrap)
to provide this functionality. The following
command sets up our REPL for the experiments in this section:

```repl
> rlwrap idris2 --find-ipkg src/Doc/Inspect.idr
```

## Quotes

We start by looking at the three types of quotes available
in Idris. All of them start with a backtick (\`) followed
by some expression wrapped in different types of parentheses.

### Names
Names (`Language.Reflection.TT.Name`)
represent identifiers in Idris expressions: Names of data types,
constructors, functions, parameters, and variables.
They can be quoted by putting an identifier in curly braces:

```repl
Doc.Inspect> :t `{ Just }
UN (Basic "Just") : Name
```

Here, Idris not only shows us the types but also the
data structure of the interpreted value. We can also
prefix names with a namespace:

```repl
Doc.Inspect> `{ Prelude.Types.Either }
NS (MkNS ["Types", "Prelude"]) (UN (Basic "Either"))
```

Note, that quoted names as well as other quoted expressions
are not interpreted any further. Names are not checked for
being in scope and expressions are neither type-checked nor
evaluated.

If we need to define our own names, it is typically safest
to use quotes as shown above. In case of possible ambiguities,
prefer fully qualified names.
If however we need to generate a name programmatically, we
will use the `UN` constructor most of the time. In addition,
module `Language.Reflection.Syntax` provides a `FromString`
instance for `Name`.

### Expressions

Probably the most important quoting facility
is the ability to quote expressions. This
results in values of type `Language.Reflection.TTImp.TTImp`.

```repl
Doc.Inspect> :t `(2 * x)
```

This will print an impressive amount of information about the structure
of the underlying syntax tree together with its type: `TTImp`.
Quite a bit of space is "wasted" on source location
information. In order to render this a bit more readable while still
trying to make the underlying tree structure visible, a
pretty printer is provided:

```repl
Doc.Inspect> :exec putPretty `(2 * x)
var "*" .$ (var "fromInteger" .$ primVal (BI 2)) .$ var "x"
```
As can be seen, source locations have been removed and `Name`s are rendered
without constructors (because there is a `FromString Name` implementation
in `Language.Reflection.Syntax`). The data constructors `IVar` and `IPrimVal`
have been replaced with functions `var` and `primVal`, respectively.
Function application is treated specially:
The TTImp constructor `IApp` has been replaced with infix operator
`(.$)` to enhance readability and reduce the amount of parentheses.
While this somewhat obfuscates how cascades of function application result in nested
calls to IApp, it is still valid Idris code, because the operator comes
from `Language.Reflection.Syntax.Ops`. This holds in general: Pretty printed
`TTImp` is valid Idris code, otherwise, that's a bug.

A similar layout is used for nested function declarations
(data constructor `IPi` and infix operator `(.->)`)
and lambdas (data constructor `ILam` and infix operator `(.=>)`):

```repl
Doc.Inspect> :exec putPretty `(Show a => (val : a) -> String)
    MkArg MW AutoImplicit Nothing (var "Show" .$ var "a")
.-> MkArg MW ExplicitArg (Just "val") (var "a")
.-> primVal (PrT StringType)
```

```repl
Doc.Inspect> :exec putPretty `(\x,y => x ++ reverse y)
    MkArg MW ExplicitArg (Just "x") implicitFalse
.=> MkArg MW ExplicitArg (Just "y") implicitFalse
.=> var "++" .$ var "x" .$ (var "reverse" .$ var "y")
```

Again, this gives a pretty clear picture about the data constructors
involved while trying to make things somewhat more readable. And again, both
examples are valid Idris syntax:

```idris
test : TTImp
test =
  lam (MkArg MW ExplicitArg (Just "x") implicitFalse) $
  lam (MkArg MW ExplicitArg (Just "y") implicitFalse) $
  var "++" .$ var "x" .$ (var "reverse" .$ var "y")
```

Below follow some more examples, including some syntactic sugar dissections.

Case expressions:

```repl
Doc.Inspect> :exec putPretty `(case x of { EQ => "eq"; LT => "lt"; GT => "gt" })
iCase
  { sc = var "x"
  , ty = implicitFalse
  , clauses =
      [ var "EQ" .= var "fromString" .$ primVal (Str "eq")
      , var "LT" .= var "fromString" .$ primVal (Str "lt")
      , var "GT" .= var "fromString" .$ primVal (Str "gt")
      ]
  }
```

Let expressions:

```repl
Doc.Inspect> :exec putPretty `(let val = show x in val == reverse val)
iLet
  { count = MW
  , name = "val"
  , type = implicitTrue
  , val = var "show" .$ var "x"
  , scope = var "==" .$ var "val" .$ (var "reverse" .$ var "val")
  }
```

If-then-else:

```repl
Doc.Inspect> :exec putPretty `(if x then y else z)
iCase
  { sc = var "x"
  , ty = var "Bool"
  , clauses = [var "True" .= var "y", var "False" .= var "z"]
  }
```

Idiom brackets:

```repl
Doc.Inspect> :exec putPretty `([| fun x y |])
var "<*>" .$ (var "<*>" .$ (var "pure" .$ var "fun") .$ var "x") .$ var "y"
```

Do notation:

```repl
Doc.Inspect> :exec putPretty `(do x <- run; action x; pure x)
   var ">>="
.$ var "run"
.$ (    MkArg MW ExplicitArg (Just "x") implicitFalse
    .=> var ">>" .$ (var "action" .$ var "x") .$ (var "pure" .$ var "x"))
```

Monad comprehensions:

```repl
Doc.Inspect> :exec putPretty `([x * x | x <- xs, even x])
   var ">>="
.$ var "xs"
.$ (    MkArg MW ExplicitArg (Just "x") implicitFalse
    .=>    var ">>"
        .$ (var "guard" .$ (var "even" .$ var "x"))
        .$ (var "pure" .$ (var "*" .$ var "x" .$ var "x")))
```

The syntactic sugar examples show that we can use these
constructs in regular code and in quoted expressions and declarations
but not when building syntax trees manually using the constructors
of `Language.Reflection.TTImp`. It can be quite useful to visualize
how these constructs are desugared by Idris.

### Declarations

Finally, it is possible to quote whole multiline declarations
by putting them in quoted brackets. In syntax files, multiline
quotes are supported:

```idris
testDecl : List Decl
testDecl = `[ export %inline
              test : Int -> Int
              test n = n + n ]
```

In the REPL, we have to separate lines by using semicolons:

```repl
...> :exec putPretty `[export %inline test : Int -> Int; test n = n + n]
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
```

As can be seen, a top-level function consists of an `IClaim`
(the function's type) and an `IDef` (the implementation).

Inspecting quoted data declarations is also possible:

```repl
...> :exec putPretty `[ data Foo t = A t | B ]
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
```

## What's next

Now that we now how Idris expressions can be defined
by means of `TTImp` and `Decl`, we can start
building them programmatically. As a first example,
we will write a [macro for defining enumerations](Enum1.md).

<!-- vi: filetype=idris2:syntax=markdown
-->
