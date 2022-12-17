# The Challenges of Parameterized Data Types

We will now try to generalize our `Generic` deriving
to at the very least support parameterized types.
In order to do so, we will analyze the structure
of several examples of parameterized and indexed
types, to figure out a normalization strategy.

## Parameters and Indices

```idris
module Doc.Generic2

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import Doc.Generic1
import Data.Vect

%language ElabReflection

export
maybeInfo : TypeInfo
maybeInfo = getInfo "Maybe"
```

First, we look at `Maybe`. It has a single type parameter `ty`, which
appears as an explicit argument to `Maybe`s type constructor
and as an implicit argument to every data constructor.

```repl
...> :exec putPretty maybeInfo
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
```

```idris
export
eitherInfo : TypeInfo
eitherInfo = getInfo "Either"
```

Next comes `Either`. As can be seen below, the order
of type parameters stays (of course) the same throughout
data constructors.

```repl
...> :exec putPretty eitherInfo
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
```

But what about indexed types? How can we distinguish those
from parameterized types? Let's have a look at `Vect`.

```idris
export
vectInfo : TypeInfo
vectInfo = getInfo "Vect"
```

```repl
...> :exec putPretty vectInfo
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
```

As can be seen, `len` is not the same across data constructors,
that is, we can learn something about `len` by pattern
matching on `Vect`. Compare this with the following record:

```idris
record ParamNat (n : Nat) where
  constructor MkParamNat
  things : Vect n String
```

Here, `n` is a parameter (of type `Nat`): We can not learn anything
about it by pattern matching on `ParamNat`.

## Parameters and Indices in `Generic`

We needed to make the above distinction between type parameters
and indices, since they affect whether we can provide a single
`Generic` implementation for a data type. In the case
of `Either`, this is straight forward:

```idris
export
Generic (Either a b) [[a],[b]] where
  from (Left a)  = Z [a]
  from (Right b) = S $ Z [b]

  to (Z [a])     = Left a
  to (S (Z [b])) = Right b
```

The same, however, is not possible for `Vect`, because
its type-level code depends on the vector's length.
Indeed, we have to write two implementations of `Generic`
to cover all possible cases:

```idris
export
Generic (Vect 0 a) [[]] where
  from Nil  = Z []
  to (Z []) = Nil

export
Generic (Vect (S k) a) [[a,Vect k a]] where
  from (h::t)  = Z [h,t]
  to (Z [h,t]) = h :: t
```

Compare this with the `Generic` instance of `ParamNat`:

```idris
export
Generic (ParamNat n) [[Vect n String]] where
  from (MkParamNat ss) = Z [ss]
  to (Z [ss])          = MkParamNat ss
```

Indeed, it seems like parameterized types are exactly those
types, for which we can come up with a single implementation
of `Generic`.

## Normalizing Parameter Names

Let's have a look at another example. `ASum` takes
two type parameters but uses different names for
parameters in its constructors.

```idris
export
data ASum : (a : Type) -> (b : Type) -> Type where
  L : x       -> ASum x y
  R : Maybe t -> ASum s t

export
sumInfo : TypeInfo
sumInfo = getInfo "ASum"
```

Idris faithfully uses the same parameter names:

```repl
..> :exec putPretty sumInfo
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
```

However, if we want to provide an implementation of `Generic`,
we have to use the same parameter name throughout:

```idris
export
Generic (ASum a b) [[a],[Maybe b]] where
  from (L a) = Z [a]
  from (R m) = S $ Z [m]

  to (Z [a])     = L a
  to (S $ Z [m]) = R m
```

So, in order to derive a single instance of `Generic` automatically,
we need to make sure that the data type in question has only
parameters but no indices, and we either need to introduce consistent
naming of parameters or reject data types with inconsistently named
parameters.

## `ParamTypeInfo`

Module `Language.Reflection.Types` provides a data type for
properly normalized information about parameterized types:
`ParamTypeInfo`:

```idris
sumParamInfo : ParamTypeInfo
sumParamInfo = getParamInfo "ASum"
```

```repl
..> :exec putPretty sumParamInfo
...
```

This produces a lot of information, which I'm not going to repeat here.
Feel free to have a look yourself.

## What's next

Now we should be ready to derive `Generic` instances
for arbitrary parameterized types. [Let's go](Generic3.md).
