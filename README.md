# idris2-elab-util
Utilities and documentation for exploring idirs2's new elaborator reflection.

## Metaprogramming

We can now use the ability to inspect the structure of
syntax trees to manipulate `TTImp`s and write our own
metaprograms.

### Enums

We often define sum times like `Weekday` below to define
a choice between concrete values.

```idris
public export
data Weekday = Monday
             | Tuesday
             | Wednesday
             | Thursday
             | Friday
             | Saturday
             | Sunday
```

We will now write a metaprogram that generates similar
structures from a list of strings.

```idris
enumDecl : (name : String) -> (vals : List String) -> Decl
```

Before we can implement `enumDecl`, we will inspect the
structure of a typical enum type in the REPL:

```
...> :exec putPretty `[data Enum = A | B | C]

  [ Data Private
         (MkData Enum IType [])
         MkTy A (IVar Enum)
         MkTy B (IVar Enum)
         MkTy C (IVar Enum) ]
                                              
```
