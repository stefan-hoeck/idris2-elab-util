# idris2-elab-util
Utilities and documentation for exploring idirs2's new elaborator reflection.

## Getting started
In order to get started with the new elaborator reflection,
[pretty printers](/src/Language/Elab/Pretty.idr)
for types found in `Language.Elab.TTImp` and `Language.Elab.TT` are provided.
These allow you to inspect quoted syntax snippets and inspect
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

Note, that quoted names as well as other quoted expressions
are not interpreted any further. Names are not checked for
being in scope and expressions are neither type-checked nor
evaluated.

### Expressions
Probably the most important quoting facility in the beginning
is the ability to quote expressions.

```
Language.Elab.Pretty> :t `(2 * x)
```

This will print quite an amount of information about the structure
of the underlying syntax tree together with its type: `TTImp`.
Quite a bit of information is "wasted" on source location
information. In order to render this a bit more readable while still
trying to make the underlying structure visible, a bunch
of pretty printers is provided:

```
Language.Elab.Pretty> :exec putPretty `(2 * x)
IVar * `app` (IVar fromInteger `app` 2) `app` IVar x
```

As can be seen, source locations have been removed, names
are rendered without their data constructors, and
function application is shown in infix notation to
reduce the amount of parentheses.
