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

  MkTypeInfo Prelude.Types.Maybe [(MW ExplicitArg ty : IType)]
    MkCon Prelude.Types.Nothing
          [(M0 ImplicitArg ty : IType)]
          (IApp. IVar Prelude.Types.Maybe $ IVar ty)
    MkCon Prelude.Types.Just
          [(M0 ImplicitArg ty : IType), (M1 ExplicitArg x : IVar ty)]
          (IApp. IVar Prelude.Types.Maybe $ IVar ty)

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


  MkTypeInfo Prelude.Types.Either
             [(MW ExplicitArg a : IType), (MW ExplicitArg b : IType)]
    MkCon Prelude.Types.Left
          [ (M0 ImplicitArg a : IType)
          , (M0 ImplicitArg b : IType)
          , (M1 ExplicitArg x : IVar a) ]
          (IApp. IVar Prelude.Types.Either $ IVar a $ IVar b)
    MkCon Prelude.Types.Right
          [ (M0 ImplicitArg a : IType)
          , (M0 ImplicitArg b : IType)
          , (M1 ExplicitArg x : IVar b) ]
          (IApp. IVar Prelude.Types.Either $ IVar a $ IVar b)

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

  MkTypeInfo Data.Vect.Vect
             [ (MW ExplicitArg len : IVar Prelude.Types.Nat)
             , (MW ExplicitArg elem : IType) ]
    MkCon Data.Vect.Nil
          [(M0 ImplicitArg elem : IType)]
          (IApp. IVar Data.Vect.Vect $ IVar Prelude.Types.Z $ IVar elem)
    MkCon Data.Vect.::
          [ (M0 ImplicitArg len : IVar Prelude.Types.Nat)
          , (M0 ImplicitArg elem : IType)
          , (M1 ExplicitArg x : IVar elem)
          , (M1 ExplicitArg xs : IApp. IVar Data.Vect.Vect
                               $ IVar len
                               $ IVar elem) ]
          (IApp. IVar Data.Vect.Vect
               $ (IApp. IVar Prelude.Types.S $ IVar len)
               $ IVar elem)

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

  MkTypeInfo Doc.Generic2.ASum
             [(MW ExplicitArg a : IType), (MW ExplicitArg b : IType)]
    MkCon Doc.Generic2.L
          [ (M0 ImplicitArg y : IType)
          , (M0 ImplicitArg x : IType)
          , (MW ExplicitArg {arg:5914} : IVar x) ]
          (IApp. IVar Doc.Generic2.ASum $ IVar x $ IVar y)
    MkCon Doc.Generic2.R
          [ (M0 ImplicitArg s : IType)
          , (M0 ImplicitArg t : IType)
          , (MW ExplicitArg {arg:5915} : IApp. IVar Prelude.Types.Maybe
                                             $ IVar t) ]
          (IApp. IVar Doc.Generic2.ASum $ IVar s $ IVar t)

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

  MkParamTypeInfo Doc.Generic2.ASum [(a, IType), (b, IType)]
    MkParamCon Doc.Generic2.L [({arg:6784}, IVar a)]
    MkParamCon Doc.Generic2.R
               [({arg:6785}, IApp. IVar Prelude.Types.Maybe $ IVar b)]


```

## What's next

Now we should be ready to derive `Generic` instances
for arbitrary parameterized types. [Let's go](Generic3.md).
