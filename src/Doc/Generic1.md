# Sums of Products: A Generic Representation for Algebraic Data Types

In Haskell, there are numerous libraries dealing with the
concept of *Generics*: Canonical representations of algebraic
data types. Different libraries differ in how they represent
data types generically and what kinds of data types
can be represented by generics.

In this series of posts I'll try to adapt several types
of representations of increasing complexity to the world
of Idris and derive these generic representations through
elaborator reflection.

## Generic Codes: A List of Lists of Types

In [generic-sop](https://hackage.haskell.org/package/generics-sop)
regular algebraic data types are represented as sums of products,
indexed by a list of lists of types (a data type's *code*).
Below is a simplified version:

```idris
module Doc.Generic1

import Language.Reflection.Pretty
import Language.Reflection.Util

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
add an additional type parameter of kind `k -> Type`
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
```

Next, we need an interface for converting from and to
generic representations of algebraic data types:

```idris
public export
interface Generic (0 t : Type) (0 code : List (List Type)) | t where
  constructor MkGeneric
  from : t -> SOP code
  to   : SOP code -> t

public export total
genEq : Generic t code => All2 Eq code => t -> t -> Bool
genEq a b = from a == from b

public export total
genCompare :
     {auto _ : Generic t code}
  -> {auto _ : All2 Eq code}
  -> {auto _ : All2 Ord code}
  -> t -> t -> Ordering
-- We don't use `comparing` here, since for the time being
-- it is not publicly exported, which makes type-level
-- testing more difficult
genCompare t1 t2 = compare (from t1) (from t2)
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
Eq Person where (==) = assert_total genEq

export
Ord Person where compare = assert_total genCompare
```

As can be seen, once we have an instance of `Generic t`,
it is trivial to derive implementations of `Eq` and other
interfaces without the need of meta programming.
Note, however, that due to the inductive nature of
`Person` it is necessary to convince the totality checker
by using `assert_total`. There doesn't seem to be a way
around this right now.

Another example, this time with a sum-type:

```idris
public export
data ParseErr =
    EOF
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
a utility to collect type arguments and constructors
of a data type as a `TypeInfo` value. We can use this
information to manually build up the `TTImp`
for an implementation of `Generic`.

Creating the `Code` is straight forward. We use utility function
`listOf` from `Language.Reflection.Syntax`, which recursively
applies the passed sequence of arguments to `(::)` and ends it
with `Nil`.

```idris
-- Creates the `List (List Type)` code for a data type.
private
mkCode : TypeInfo -> TTImp
mkCode ti = listOf $ map (\c => listOf $ type <$> c.args) ti.cons
```

For the pattern clauses in the implementation of `from`
and `to`, we need to keep track of the index of the
actual constructor and create the `SOP` value according
to this index.

```idris
||| Applies the proper n-ary sum constructor to an argument
||| of arguments. `k` is the level of nesting used
export
mkSOP1 : (k : Nat) -> (arg : TTImp) -> TTImp
mkSOP1 0     arg = `(Z ~(arg))
mkSOP1 (S k) arg = `(S ~(mkSOP1 k arg))

||| Applies the proper n-ary sum constructor to a list
||| of arguments. `k` is the level of nesting used.
export
mkSOP : Foldable t => (k : Nat) -> (args : t TTImp) -> TTImp
mkSOP k = mkSOP1 k . listOf

export
zipWithIndex : List a -> List (Nat,a)
zipWithIndex as = run 0 as

  where
    run : Nat -> List a -> List (Nat,a)
    run _ []     = []
    run k (h::t) = (k,h) :: run (S k) t
```

For the implementations of functions `from` and `to`,
we need to generate pattern clauses for every data
constructor. We collect the required constructor
name and generated list of fresh argument names in a tuple:

```idris
||| Constructor name and names of arguments
||| to be used in pattern match declarations
public export
ConNames : Type
ConNames = (Name, List String, List TTImp)

private
conNames : (c : Con n vs) -> ConNames
conNames c =
  let ns   := toList $ freshNames "x" c.arty
      vars := map varStr ns
   in (c.name, ns, vars)

export
fromClause : (Nat,ConNames) -> Clause
fromClause (k,(con,ns,vars)) = patClause (bindAll con ns) (mkSOP k vars)

export
toClause : (Nat,ConNames) -> Clause
toClause (k,(con,ns,vars)) =
  patClause (mkSOP k $ map bindVar ns) (appAll con vars)

export
toClauses : List (Nat,ConNames) -> List Clause
toClauses cs =
  map toClause cs ++
  -- in certain pathological cases, the coverage checker can not
  -- determine on its own that the above list of clauses is covering.
  -- we therefore append an explicit `impossible` clause.
  [impossibleClause $ mkSOP1 (length cs) implicitTrue]
```

A quick note about function `nameStr`: Idris does not accept
the machine-generated names of unnamed arguments in pattern matches.
The function `nameStr` converts such names to similar user-defined names.

```idris
private
genericDecl : TypeInfo -> List Decl
genericDecl ti =
  let -- constructor names
      names    := zipWithIndex (map conNames ti.cons)

      -- name of implementation function
      function := UN . Basic $ "implGeneric" ++ camelCase (name ti)

      -- type of implementation function
      funType := `(Generic ~(var $ name ti) ~(mkCode ti))

      -- implementation of from and to as anonymous functions
      x       := lambdaArg {a = Name} "x"
      varX    := var "x"
      from    := lam x $ iCase varX implicitFalse (map fromClause names)
      to      := lam x $ iCase varX implicitFalse (toClauses names)

   in [ interfaceHint Public function funType
      , def function [patClause (var function) (appAll "MkGeneric" [from,to])]
      ]
```

Let's break this down a bit: We first get access
to the data type's constructor and argument names
and calculate the name
of our implementation function. We then calculate
the implementation's type by applying our data type and
generated code to the type constructor `Generic`.
The actual implementation consists of functions `from`
and `to`, both implemented as anonymous functions
with a pattern clause for each data constructor.
Finally, we return the type declaration of
the implementation function together with the actual
function definition consisting of a single pattern clause.

The only thing still missing is an `Elab` function
to actually have the elaborator include our derived
instances:

```idris
private
deriveGeneric : Name -> Elab ()
deriveGeneric name = getInfo' name >>= declare . genericDecl
```

OK, let's give this a spin:

```idris
private
record Employee where
  constructor MkEmployee
  name       : String
  age        : Int
  salary     : Double
  supervisor : Maybe Employee

%runElab (deriveGeneric "Employee")

private
Eq Employee where (==) = assert_total genEq

private
Ord Employee where compare = assert_total genCompare

-- Just being able to write the type of this function like this
-- is amazing. :-)
private
empTest1 : let emp = MkEmployee "" 20 1.2 Nothing in (emp == emp) = True
empTest1 = Refl

private
empTest2 :
  ( MkEmployee "" 20 1.2 Nothing < MkEmployee "" 21 1.2 Nothing) = True
empTest2 = Refl
```

And with a sum type:

```idris
private
data Request =
    Login String String
  | Add Employee
  | Delete Employee
  | Logout

%runElab (deriveGeneric "Request")

private
Eq Request where (==) = genEq

private
Ord Request where compare = genCompare

private
reqTest1 : Login "" "" /= Logout = True
reqTest1 = Refl

private
reqTest2 : Logout > Login "" "" = True
reqTest2 = Refl
```

## What's next

The above implementation is very basic and error prone.
We can not deal with parameterized or indexed types, nor
with existentials and dependent types. There will be
no coherent error messages if we derive a `Generic`
instance for one of these classes of data types.
Additionally, since we already have the necessary information
available, it would be great to use constructor and
argument names to derive instances for `Show` or JSON
marshallers. In the [next part](Generic2.md), we will
first analyze the challenges coming with parameterized
and indexed types.

<!-- vi: filetype=idris2:syntax=markdown
-->
