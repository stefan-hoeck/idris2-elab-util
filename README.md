# idris2-elab-util
Utilities and documentation for exploring idirs2's new elaborator reflection.

## Getting started
In order to get started with the new elaborator reflection,
[pretty printers](/src/Language/Elab/Pretty.idr)
for types found in `Language.Elab.TTImp` and `Language.Elab.TT` are provided.
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
IVar * `app` (IVar fromInteger `app` 2) `app` IVar x
```

As can be seen, source locations have been removed, names
are rendered without constructors, and
function application is shown in infix notation to
reduce the amount of parentheses.

We can also inspect type declarations:

```
Language.Elab.Pretty> :exec putPretty `(Show a => (val : a) -> String)
pi :  (MW AutoImplicit  : IVar Show `app` IVar a)
   -> (MW ExplicitArg val : IVar a)
   -> String
```

Lambdas:

```
Language.Elab.Pretty> :exec putPretty `(\x,y => x ++ reverse y)
lambda :  (MW ExplicitArg x : {Implicit:False})
       => (MW ExplicitArg y : {Implicit:False})
       => IVar ++ `app` IVar x `app` (IVar reverse `app` IVar y)
```

Case expressions:

```
Language.Elab.Pretty> :exec putPretty `(case x of { EQ => "eq"; LT => "lt"; GT => "gt" })
case (IVar x : {Implicit:False}) of
  pattern IVar EQ => IVar fromString `app` eq
  pattern IVar LT => IVar fromString `app` lt
  pattern IVar GT => IVar fromString `app` gt
```

Now follow some syntactic sugar exaples.
If-then-else:

```
Language.Elab.Pretty> :exec putPretty `(if x then y else z)
case (IVar x : IVar Bool) of
  pattern IVar True = IVar y
  pattern IVar False = IVar z
```

Idiom brackets:

```
Language.Elab.Pretty> :exec putPretty `([| fun x y |])
IVar <*> `app` ((IVar <*> `app` (IVar pure `app` IVar fun)) `app` IVar x) `app`
IVar y
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
of `Language.Elab.TTImp`.
