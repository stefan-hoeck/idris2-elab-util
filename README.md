# idris2-elab-util
Utilities and documentation for exploring idirs2's new elaborator reflection.

## Getting started
In order to get started with the new elaborator reflection,
[pretty printers](/src/Language/Elab/Pretty.idr)
for types found in `Language.Reflection.TTImp` and `Language.Reflection.TT` are provided.
These allow us to inspect quoted syntax snippets and visualize
how they are internally converted to `Name`s, `TTImp`s or `Decl`s.

Since the idris2 REPL does not yet support using the arrow keys
to scroll through its command history, `rlwrap` can be used as a substitute.
The following shell command sets up your REPL for some first experiments:

```
$ rlwrap idris2 --source-dir src src/Language/Elab/Pretty.idr
```

## Inspecting quotes
There are three types of quotes available at the moment.
All of them start with a single backtick (\`).

### Names
Names can be quoted by putting an identifier in double
curly braces:

```
Language.Elab.Pretty> :t `{{ Just }}
UN "Just" : Name
```

Here, idris not only shows us the types but also the
data stucture of the interpreted value. We can also
prefix names with a namespace:

```
Language.Elab.Pretty> `{{ Prelude.Types.Either }}
NS (MkNS ["Types", "Prelude"]) (UN "Either")
```

Note that quoted names as well as other quoted expressions
are not interpreted any further. Names are not checked for
being in scope and expressions are neither type-checked nor
evaluated.

### Expressions
Probably the most important quoting facility
is the ability to quote expressions.

```
Language.Elab.Pretty> :t `(2 * x)
```

This will print an impressive amount of information about the structure
of the underlying syntax tree together with its type: `TTImp`.
Quite a bit of space is "wasted" on source location
information. In order to render this a bit more readable while still
trying to make the underlying structure visible, a
pretty printer is provided:

```
Language.Elab.Pretty> :exec putPretty `(2 * x)

  IApp. IVar * $ (IApp. IVar fromInteger $ IPrimVal 2) $ IVar x

```

As can be seen, source locations have been removed and names
are rendered without constructors. Function application is
treated specially: The data constructor `IApp` is shown, to
tell users which constructor to use, but nested calls to `IApp`
are then replaced with an infix operater (`$`) to enhance readability
and reduce the amount of parentheses. While this somewhat obfuscates
how cascades of function application result in nested calls
to `IApp`, it helps when verifying the correct structure of our own
manually written `TTImp` values.

A similar layout is used for nested function declarations
and lambdas:

```
Language.Elab.Pretty> :exec putPretty `(Show a => (val : a) -> String)

  IPi.  (MW AutoImplicit : IApp. IVar Show $ IVar a)
     -> (MW ExplicitArg val : IVar a)
     -> IPrimVal String

```

```
Language.Elab.Pretty> :exec putPretty `(\x,y => x ++ reverse y)

  ILam.  (MW ExplicitArg x : IImplicit False)
      => (MW ExplicitArg y : IImplicit False)
      => (IApp. IVar ++ $ IVar x $ (IApp. IVar reverse $ IVar y))

```

Again, this gives a pretty clear picture about the data constructors
involved while trying to make things somewhat more readable.

Case expressions:

```
Language.Elab.Pretty> :exec putPretty `(case x of { EQ => "eq"; LT => "lt"; GT => "gt" })

  ICase (IVar x) (IImplicit False)
    PatClause (IVar EQ) (IVar fromString `IApp` IPrimVal eq)
    PatClause (IVar LT) (IVar fromString `IApp` IPrimVal lt)
    PatClause (IVar GT) (IVar fromString `IApp` IPrimVal gt)

```

Now follow some syntactic sugar exaples.
If-then-else:

```
Language.Elab.Pretty> :exec putPretty `(if x then y else z)

  ICase (IVar x) (IVar Bool)
    PatClause (IVar True) (IVar y)
    PatClause (IVar False) (IVar z)

```

Idiom brackets:

```
Language.Elab.Pretty> :exec putPretty `([| fun x y |])

         IVar <*>
  `IApp` (IVar <*> `IApp` (IVar pure `IApp` IVar fun) `IApp` IVar x)
  `IApp` IVar y

```

Do notation:

```
Language.Elab.Pretty> :exec putPretty `(do x <- run; action x; pure x)
IVar >>= `app` IVar run `app`
(lambda :  (MW ExplicitArg x : {Implicit:False})
        => IVar >>= `app` (IVar action `app` IVar x) `app`
        (lambda :  (MW ExplicitArg  : {Implicit:False})
                => IVar pure `app` IVar x))

```

The examples about special syntax show that we can use these
constructs in regular code and in quoted expressions and declarations
but not when building syntax trees manually using the constructors
of `Language.Reflection.TTImp`.
