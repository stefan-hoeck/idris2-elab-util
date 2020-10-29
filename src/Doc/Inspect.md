## Inspecting Idris Expressions

In this section of the tutorial we will learn how
to look at the underlying structure of Idris expressions.
Most of the examples can be run from the REPL.

To better visualize the sometimes deeply nested
syntax trees, [pretty printers](../Language/Reflection/Pretty.idr)
are provided for all public
data types in modules `Language.Reflection.TT` and
`Language.Reflection.TTImp`.

Since the Idris REPL does not yet support scrolling
through its command history, I suggest using the
command line utility [rlwrap](https://github.com/hanslub42/rlwrap)
to provide this functionality. The following
command sets up our REPL for the experiments in this section:

```
$ rlwrap idris2 --source-dir src src/Language/Reflection/Pretty.idr
```

### Quotes

We start by looking at the three types of quotes available
in Idris. All of them start with a backtick (\`) followed
by some expression wrapped in different types of parentheses.

#### Names
Names (`Language.Reflection.TT.Name`)
represent identifiers in Idris expressions: Names of data types,
constructors, functions, parameters, and variables.
They can be quoted by putting an identifier in double
curly braces:

```
Language.Reflection.Pretty> :t `{{ Just }}
UN "Just" : Name
```

Here, Idris not only shows us the types but also the
data stucture of the interpreted value. We can also
prefix names with a namespace:

```
Language.Reflection.Pretty> `{{ Prelude.Types.Either }}
NS (MkNS ["Types", "Prelude"]) (UN "Either")
```

Note, that quoted names as well as other quoted expressions
are not interpreted any further. Names are not checked for
being in scope and expressions are neither type-checked nor
evaluated.

If we need to define our own names, it is typically safest
to use quotes as shown above. In case of possible ambiguities,
prefer fully qualified names.
If however we need to generate a name programmatically, we
will use the `UN` constructor most of the time.

#### Expressions

Probably the most important quoting facility
is the ability to quote expressions.

```
Language.Reflection.Pretty> :t `(2 * x)
```

This will print an impressive amount of information about the structure
of the underlying syntax tree together with its type: `TTImp`.
Quite a bit of space is "wasted" on source location
information. In order to render this a bit more readable while still
trying to make the underlying tree structure visible, a
pretty printer is provided:

```
Language.Reflection.Pretty> :exec putPretty `(2 * x)

  IApp. IVar * $ (IApp. IVar fromInteger $ IPrimVal 2) $ IVar x

```

As can be seen, source locations have been removed and `Name`s
are rendered without constructors. Function application is
treated specially: The `TTImp` constructor `IApp` is shown to
tell users which constructor was used, but nested calls to `IApp`
are then replaced with an infix operater (`$`) to enhance readability
and reduce the amount of parentheses. While this somewhat obfuscates
how cascades of function application result in nested calls
to `IApp`, it helps when verifying the correct structure of our own
manually written `TTImp` values.

A similar layout is used for nested function declarations
(data constructor `IPi` and nesting operator `->`)
and lambdas (data constructor `ILam` and nesting
operator `=>`):

```
Language.Reflection.Pretty> :exec putPretty `(Show a => (val : a) -> String)

  IPi.  (MW AutoImplicit : IApp. IVar Show $ IVar a)
     -> (MW ExplicitArg val : IVar a)
     -> IPrimVal String

```

```
Language.Reflection.Pretty> :exec putPretty `(\x,y => x ++ reverse y)

  ILam.  (MW ExplicitArg x : IImplicit False)
      => (MW ExplicitArg y : IImplicit False)
      => (IApp. IVar ++ $ IVar x $ (IApp. IVar reverse $ IVar y))

```

Again, this gives a pretty clear picture about the data constructors
involved while trying to make things somewhat more readable.

Below follow some more examples, including some
syntactic sugar dissections.

Case expressions:

```
Language.Reflection.Pretty> :exec putPretty `(case x of { EQ => "eq"; LT => "lt"; GT => "gt" })

  ICase (IVar x)
        (IImplicit False)
        [ PatClause (IVar EQ) (IApp. IVar fromString $ IPrimVal eq)
        , PatClause (IVar LT) (IApp. IVar fromString $ IPrimVal lt)
        , PatClause (IVar GT) (IApp. IVar fromString $ IPrimVal gt) ]

```

Let expressions:

```
Language.Reflection.Pretty> :exec putPretty `(let val = show x in val == reverse val)

  ILet MW
       val
       (Implicit True)
       (IApp. IVar show $ IVar x)
       (IApp. IVar == $ IVar val $ (IApp. IVar reverse $ IVar val))

```

If-then-else:

```
Language.Reflection.Pretty> :exec putPretty `(if x then y else z)

  ICase (IVar x)
        (IVar Bool)
        [PatClause (IVar True) (IVar y), PatClause (IVar False) (IVar z)]

```

Idiom brackets:

```
Language.Reflection.Pretty> :exec putPretty `([| fun x y |])

  IApp. IVar <*>
      $ (IApp. IVar <*> $ (IApp. IVar pure $ IVar fun) $ IVar x)
      $ IVar y


```

Do notation:

```
Language.Reflection.Pretty> :exec putPretty `(do x <- run; action x; pure x)

App. IVar >>=
   $ IVar run
   $ (ILam.  (MW ExplicitArg x : IImplicit False)
          => (IApp. IVar >>=
                  $ (IApp. IVar action $ IVar x)
                  $ (ILam.  (MW ExplicitArg : IImplicit False)
                         => (IApp. IVar pure $ IVar x))))

```

Monad comprehensions:

```
Language.Reflection.Pretty> :exec putPretty `([x * x | x <- xs, even x])

  IApp. IVar >>=
      $ IVar xs
      $ (ILam.  (MW ExplicitArg x : Implicit False)
             => (IApp. IVar >>=
                     $ (IApp. IVar guard $ (IApp. IVar even $ IVar x))
                     $ (ILam.  (MW ExplicitArg : Implicit False)
                            => (IApp. IVar pure
                                    $ (IApp. IVar * $ IVar x $ IVar x)))))

```

The syntactic sugar examples show that we can use these
constructs in regular code and in quoted expressions and declarations
but not when building syntax trees manually using the constructors
of `Language.Reflection.TTImp`. It can be quite useful to visualize
how these constructs are desugared by Idris.

#### Declarations

Finally, it is possible to quote whole multiline declarations
by putting them in quoted bracktes. In syntax files, multiline
quotes are supported:

```idris
module Doc.Inspect

import Language.Reflection

testDecl : List Decl
testDecl = `[ export %inline
              test : Int -> Int
              test n = n + n ]
```

In the REPL, we have to separate lines by using semicolons:

```
...> :exec putPretty `[export %inline test : Int -> Int; test n = n + n]

  [ IClaim MW
           Export
           [Inline]
           (MkTy test (IPi. (MW ExplicitArg : IPrimVal Int) -> IPrimVal Int))
  , IDef test
         [ PatClause (IApp. IVar test $ IBindVar n)
                     (IApp. IVar + $ IVar n $ IVar n) ] ]

```

As can be seen, a top-level function consists of an `IClaim`
(the function's type) and and `IDef` (the implementation).

Inspecting quoted data declarations is also possible:

```
...> :exec putPretty `[ data Foo t = A t | B ]

  [ IData Private
          (MkData Foo
                  (IPi. (M1 ExplicitArg : IType) -> IType)
                  []
                  [ MkTy A
                         (IPi.  (M1 ExplicitArg : IBindVar t)
                             -> (IApp. IVar Foo $ IBindVar t))
                  , MkTy B (IApp. IVar Foo $ IBindVar t)] ]

```

### What's next

Now that we now how Idris expressions can be expressed
by means of `TTImp` and `Decl`, we can start
building them programmatically. As a first example,
we will write a [macro for defining enumerations](Enum1.md).
