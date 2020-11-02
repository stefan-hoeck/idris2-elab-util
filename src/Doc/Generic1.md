## Generics Part 1

In Haskell, there are numerous libraries dealing with the
concept of *Generics*: Canonical representations of algebraic
data types. Different libraries differ in how the represent
data types generically and what kinds of data types
can be represented by generics.

In this series of posts I'll try to adabt several types
of representations of increasing complexity to the world
of Idris and derive these generic representations through
elaborator reflection.

### Generic Codes: A List of Lists of Types

[generic-sop](https://hackage.haskell.org/package/generics-sop)
represent regular algebraic data types as a sum of products,
indexed by a list of lists of types (a data types *code*).
Below is a simplified version:

```idris
public export
data NP : (ts : List Type) -> Type where
  Nil : NP []
  (::) : (val : t) -> (vals : NP ts) -> NP (t :: ts)

public export
data SOP : (tss : List (List Type)) -> Type where
  Z : NP ts   -> SOP (ts :: tss)
  S : SOP tss -> SOP (ts :: tss)
```

The actual types in *generic-sop* are kind-polymorphic and
add an additional type parameter of kind `Type -> Type`
to allow for many powerful higher-order manipulations.
We might return to that more versatile representation later on.

With two additional utility functions, we can start implementing
different typeclasses for `SOP`:

```idris
public export
All : (f : Type -> Type) -> (ts : List Type) -> Type
All f [] = ()
All f (t::ts) = (f t, All f ts)

public export
All2 : (f : Type -> Type) -> (tss : List(List Type)) -> Type
All2 f [] = ()
All2 f (ts::tss) = (All f ts, All2 f tss)

public export
All Eq ts => Eq (NP ts) where
  Nil == Nil               = True
  (h1 :: t1) == (h2 :: t2) = h1 == h2 && t1 == t2

public export
All2 Eq tss => Eq (SOP tss) where
  Z v1 == Z v2 = v1 == v2
  S v1 == S v2 = v1 == v2
  _    == _    = False

public export
(All Eq ts, All Ord ts) => Ord (NP ts) where
  compare Nil Nil               = EQ
  compare (h1 :: t1) (h2 :: t2) = compare h1 h2 <+> compare t1 t2

public export
All2 Eq tss => All2 Ord tss => Ord (SOP tss) where
  compare (Z v1) (Z v2) = compare v1 v2
  compare (S v1) (S v2) = compare v1 v2
  compare (Z _ ) (S _)  = LT
  compare (S _ ) (Z _)  = GT

public export
All Semigroup ts => Semigroup (NP ts) where
  Nil <+> Nil               = Nil
  (h1 :: t1) <+> (h2 :: t2) = (h1 <+> h2) :: (t1 <+> t2)

public export
All Semigroup ts => Semigroup (SOP [ts]) where
  (Z v1) <+> (Z v2) = Z $ v1 <+> v2

public export
{ts : _} -> All Semigroup ts => All Monoid ts => Monoid (NP ts) where
  neutral {ts = Nil}    = Nil
  neutral {ts = (_::_)} = neutral :: neutral
```

Next, we need a data type for generic representations of algebraic
data types:

```idris
public export
record Generic t where
  constructor MkGeneric
  code' : List (List Type)
  from' : t -> SOP code'
  to'   : SOP code' -> t

public export
Code : (t : Type) -> (prf : Generic t) => List (List Type)
Code _ = code' prf

public export
from : (prf : Generic t) => t -> SOP (Code t)
from = from' prf

public export
to : (prf : Generic t) => SOP (Code t) -> t
to = to' prf

public export
genEq : Generic t => All2 Eq (Code t) => t -> t -> Bool
genEq a b = from a == from b

public export
genCompare :  Generic t
           => All2 Eq (Code t)
           => All2 Ord (Code t)
           => t -> t -> Ordering
genCompare a b = comparing from a b
```

We do not use an interface for this to make it more accessible
during elaborator reflection.

I'll now give two examples, showing how we can encode regular
data types generically.

```idris
public export
record Person where
  constructor MkPerson
  name     : String
  age      : Int
  children : List Person

public export %hint
GenericPerson : Generic Person
GenericPerson = MkGeneric [[String,Int,List Person]]
                          (\(MkPerson n a cs) => Z [n,a,cs])
                          (\(Z [n,a,cs]) => MkPerson n a cs)

export
Eq Person where (==) = genEq

export
Ord Person where compare = genCompare
```

As can be seen, once we have an instance of `Generic t`,
it is trivial to derive implementations of `Eq` and other
typeclasses without the need of meta programming.

Another example with a sum-type:

```idris
public export
data ParseErr = EOF
              | ReadErr Int Int String
              | UnmatchedParen Int Int

public export %hint
GenericParseErr : Generic ParseErr
GenericParseErr = MkGeneric Cde f t
  where Cde : List (List Type)
        Cde = [[],[Int,Int,String],[Int,Int]]

        f : ParseErr -> SOP Cde
        f EOF                  = Z []
        f (ReadErr r c msg)    = S $ Z [r,c,msg]
        f (UnmatchedParen r c) = S $ S $ Z [r,c]

        t : SOP Cde -> ParseErr
        t (Z [])            = EOF
        t (S (Z [r,c,msg])) = ReadErr r c msg
        t (S (S (Z [r,c]))) = UnmatchedParen r c

export
Eq ParseErr where (==) = genEq

export
Ord ParseErr where compare = genCompare
```

As can be seen, writing an instance of `Generic t` is
very easy but quite noisy. It should be possible to derive
such instances automatically. For this, we need to
have a look at the `TTImp` structure of data types.
