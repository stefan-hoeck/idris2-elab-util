## Generics Part 1

In Haskell, there are numerous libraries dealing with the
concept of *Generics*: Canonical representations of algebraic
data types. Different libraries differ in how they represent
data types generically and what kinds of data types
can be represented by generics.

In this series of posts I'll try to adabt several types
of representations of increasing complexity to the world
of Idris and derive these generic representations through
elaborator reflection.

### Generic Codes: A List of Lists of Types

In [generic-sop](https://hackage.haskell.org/package/generics-sop)
regular algebraic data types are represented as sums of products,
indexed by a list of lists of types (a data type's *code*).
Below is a simplified version:

```idris
module Doc.Generic1

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types

%language ElabReflection

||| An n-ary product type. This is of course
||| identical to `HVect`, unlike the version in
||| generic-sop, which is kind-polymorphic and parameterized
||| by an additional type constructor.
public export
data NP : (ts : List Type) -> Type where
  Nil : NP []
  (::) : (val : t) -> (vals : NP ts) -> NP (t :: ts)

||| An n-ary sum of products.
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
interfaces for `SOP`:

```idris
||| Witness that all elements in a list of types have
||| implementations of the given interface.
public export
All : (f : Type -> Type) -> (ts : List Type) -> Type
All f [] = ()
All f (t::ts) = (f t, All f ts)

||| Witness that all elements in a list of lists of types have
||| implementations of the given interface.
public export
All2 : (f : Type -> Type) -> (tss : List(List Type)) -> Type
All2 f [] = ()
All2 f (ts::tss) = (All f ts, All2 f tss)

public export
All Eq ts => Eq (NP ts) where
  Nil        == Nil        = True
  (h1 :: t1) == (h2 :: t2) = h1 == h2 && t1 == t2

public export
All2 Eq tss => Eq (SOP tss) where
  Z v1 == Z v2 = v1 == v2
  S v1 == S v2 = v1 == v2
  _    == _    = False

public export
All Eq ts => All Ord ts => Ord (NP ts) where
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
interface Generic (t : Type) (code : List (List Type)) | t where
  from : t -> SOP code
  to   : SOP code -> t

public export
genEq : Generic t code => All2 Eq code => t -> t -> Bool
genEq a b = from a == from b

public export
genCompare :  Generic t code
           => All2 Eq code
           => All2 Ord code
           => t -> t -> Ordering
genCompare = comparing from
```

I'll now give two examples, showing how we can encode regular
data types generically.

```idris
public export
record Person where
  constructor MkPerson
  name     : String
  age      : Int
  children : List Person

public export
Generic Person [[String,Int,List Person]] where
  from (MkPerson n a cs) = Z [n,a,cs]
  to (Z [n,a,cs]) = MkPerson n a cs

export
Eq Person where (==) = genEq

export
Ord Person where compare = genCompare
```

As can be seen, once we have an instance of `Generic t`,
it is trivial to derive implementations of `Eq` and other
typeclasses without the need of meta programming.

Another example, this time with a sum-type:

```idris
public export
data ParseErr = EOF
              | ReadErr Int Int String
              | UnmatchedParen Int Int

public export
Generic ParseErr [[],[Int,Int,String],[Int,Int]] where
  from EOF                  = Z []
  from (ReadErr r c msg)    = S $ Z [r,c,msg]
  from (UnmatchedParen r c) = S $ S $ Z [r,c]

  to (Z [])            = EOF
  to (S (Z [r,c,msg])) = ReadErr r c msg
  to (S (S (Z [r,c]))) = UnmatchedParen r c

export
Eq ParseErr where (==) = genEq

export
Ord ParseErr where compare = genCompare
```

As can be seen, writing instances of `Generic t` is
very easy but quite verbose. It should be possible to derive
such instances automatically. For this, we need to
have a look at the `TTImp` structure of data types.
Module `Language.Reflection.Types` provides `getInfo`,
a utility to to collect type arguments and constructors
of a data type as a `TypeInfo` value. We can use this
information to manually build up the `TTImp`
for an implementation of `Generic`.

Creating the `Code` is straight forward. We use utility function
`listOf` from `Language.Reflection.Syntax`, which recursively
applies the passed list of arguments to `(::)` and ends it with `Nil`.

```idris
||| Creates the `List (List Type)` code for a data type.
export
mkCode : TypeInfo -> TTImp
mkCode = listOf . map (listOf . map type . args) . cons
```

For the pattern clauses in the implementation of `from'`
and `to'`, we need to keep track of the index of the
actual constructor and create the `SOP` value according
to this index.

```idris 

private fromImpl : Name
fromImpl = "fromImpl"

private toImpl : Name
toImpl = "toImpl"

||| Applies the proper n-ary sum constructor to a list
||| of arguments. `k` is the index of the data type's
||| constructor.
export
mkSOP : (n : Int) -> (args : List TTImp) -> TTImp
mkSOP n args     = if n <= 0 then `(Z) .$ listOf args
                             else `(S) .$ mkSOP (n-1) args

||| Implements function `from'`.
export
mkFrom : TypeInfo -> List Clause
mkFrom = map cl . zipWithIndex . cons
  where cl : (Int,Con) -> Clause
        cl (n,c) = let names = argNames $ args c
                    in var fromImpl .$ appAll (name c) (map UN names) .=
                       mkSOP n (map varStr names)

||| Implements function `from'`.
export
mkTo : TypeInfo -> List Clause
mkTo = map cl . zipWithIndex . cons
  where cl : (Int,Con) -> Clause
        cl (n,c) = let names = argNames $ args c
                    in var toImpl .$ mkSOP n (map varStr names) .=
                       appAll (name c) (map UN names)
```

```idris
genericDecl1 : TypeInfo -> List Decl
genericDecl1 ti =
  let -- Names
      mkGeneric = singleCon "Generic"
      function  = UN $ "implGeneric" ++ camelCase (name ti)

      -- Vars
      myType   = arg $ var (name ti)

      cde   = mkCode ti

      impl  = local [ private' fromImpl $ myType .-> `(SOP) .$ cde
                    , def fromImpl (mkFrom ti)

                    , private' toImpl $ arg (`(SOP) .$ cde) .-> type myType
                    , def toImpl (mkTo ti)
                    ] (appAll mkGeneric [fromImpl, toImpl])

   in [ interfaceHint Public function (`(Generic) .$ type myType .$ mkCode ti)
      , def function [ var function .= impl ] ]

mkGeneric1 : Name -> Elab ()
mkGeneric1 name = getInfo' name >>= declare . genericDecl1
```

OK, let's give this a spin:

```idris
export
record Employee where
  constructor MkEmployee
  name       : String
  age        : Int
  salary     : Double
  supervisor : Maybe Employee

%runElab (mkGeneric1 "Employee")
 
export
Eq Employee where (==) = genEq

export
Ord Employee where compare = genCompare
```

And with a sum type:

```idris
export
data Request = Login String String
             | Add Employee
             | Delete Employee
             | Logout

%runElab (mkGeneric1 "Request")

export
Eq Request where (==) = genEq

export
Ord Request where compare = genCompare
```

### What's next

The above implementation is very basic and error prone.
We can not deal with parameterized or indexed types, nor
with existentials and dependent types. There will be
no coherent error messages if we derive a `Generic`
instance for one of these classes of data types.
Additionally, since we already have the necessary information
available, it would be great to use constructor and
argument names to derive instances for `Show` or JSON
marshallers.
