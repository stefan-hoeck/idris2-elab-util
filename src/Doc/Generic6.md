# Verified Interfaces Part 1

I've been planning to write this part of the tutorial
about generics for quite some time, but the writing
didn't go as smoothly as I thought it would. In the end I had
to change how interfaces for `NP` and `SOP` were defined, experience
some unexpectedly long compilation times on the run, and change
implementations once again, before I arrived at the solution
presented in this post.

So here it is, the first part of the - for the time being - final post on
interface deriving using elaborator reflection. It will be
rather lengthy with quite a bit of code repetition from earlier
posts and its focus will probably not so much be on
elaborator reflection as on Idris2 itself and some of its quirks.

```idris
module Doc.Generic6
```

## Verified `Eq`

When we are deriving interface implementations via `Generic`,
we do so in a deterministic, predictable manner. It should therefore
be possible - and desirable! - to at the same time prove
that our implementations adhere to the common laws expected
for these interfaces. As an example, let's come up with some laws
for `Eq`:

```idris
public export
IsEq : Eq a => (x,y : a) -> Type
IsEq x y = x == y = True

public export
interface Eq a => EqV a where
  total eqRefl   : (x : a) -> IsEq x x
  total eqSym    : (x,y : a) -> (x == y) = (y == x)
  total eqTrans  : (x,y,z : a) -> IsEq x y -> IsEq y z -> IsEq x z
  total neqNotEq : (x,y : a) -> (x /= y) = not (x == y)
```

So, we expect `(==)` to be reflexive, symmetric and transitive,
and we expect `(/=)` to be the negation of `(==)`. Already from
this set of axioms, some lemmas can be derived. For instance
the symmetry of `(/=)`:

```idris
public export
total
neqSym : EqV a => (x,y : a) -> (x /= y) = (y /= x)
neqSym x y =
     rewrite (neqNotEq x y)
  in rewrite (neqNotEq y x)
  in cong not (eqSym x y)
```

Let's write some implementations:

```idris
export
EqV () where
  eqRefl   ()                 = Refl
  eqSym    () ()              = Refl
  eqTrans  () () () Refl Refl = Refl
  neqNotEq _  _               = Refl

export
EqV Bool where
  eqRefl  True          = Refl
  eqRefl  False         = Refl

  eqSym   True True      = Refl
  eqSym   False False    = Refl
  eqSym   True False     = Refl
  eqSym   False True     = Refl

  eqTrans True  True  True  Refl Refl = Refl
  eqTrans False False False Refl Refl = Refl
  eqTrans True False _ _ _ impossible
  eqTrans False True _ _ _ impossible
  eqTrans _ True False _ _ impossible
  eqTrans _ False True _ _ impossible

  neqNotEq _ _ = Refl

export
EqV a => EqV (Maybe a) where
  eqRefl Nothing  = Refl
  eqRefl (Just x) = (eqRefl x)

  eqSym Nothing Nothing   = Refl
  eqSym Nothing (Just x)  = Refl
  eqSym (Just x) Nothing  = Refl
  eqSym (Just x) (Just y) = (eqSym x y)

  eqTrans Nothing  Nothing  Nothing  _   _  = Refl
  eqTrans (Just x) (Just y) (Just z) xy  yz = eqTrans x y z xy yz
  eqTrans _ Nothing (Just z) _  _ impossible
  eqTrans _ (Just _) Nothing x  y impossible
  eqTrans Nothing (Just _) _ _  _ impossible
  eqTrans (Just _) Nothing _ _  _ impossible

  neqNotEq _ _ = Refl
```

Great. A bit verbose, but we only have to write these proofs
once. We might want to sprinkle in some implementations
for primitives for good measure. For those, we have to
convince Idris that we actually know what we are doing
(I typically don't know what I'm doing, so if somebody
thinks that this is the wrong way to write implementations
of `EqV` for primitives, please let me know!).

```idris
export
EqV Int where
  eqRefl  x         = believe_me (Refl {x})
  eqSym   x y       = believe_me (Refl {x})
  eqTrans x y z v w = believe_me (Refl {x})
  neqNotEq _ _      = Refl

export
EqV String where
  eqRefl  x         = believe_me (Refl {x})
  eqSym   x y       = believe_me (Refl {x})
  eqTrans x y z v w = believe_me (Refl {x})
  neqNotEq _ _      = Refl

export
EqV Integer where
  eqRefl  x         = believe_me (Refl {x})
  eqSym   x y       = believe_me (Refl {x})
  eqTrans x y z v w = believe_me (Refl {x})
  neqNotEq _ _      = Refl

export
EqV Double where
  eqRefl  x         = believe_me (Refl {x})
  eqSym   x y       = believe_me (Refl {x})
  eqTrans x y z v w = believe_me (Refl {x})
  neqNotEq _ _      = Refl
```

However, the two most important pieces for a deriving strategy
for `EqV` are still missing: Sums and products, the
core building blocks of algebraic data types. Let's
add those. It turns out that the instance for pairs
requires us to deal with the laziness of the `(&&)`
operator. We provide two utility functions for
handling this (I got the idea for these from `Data.So`
in *base*):

```idris
public export
fromAnd : {a,b : _} -> a && Delay b = True -> (a = True, b = True)
fromAnd {a = True}  {b = True}  refl = (Refl, Refl)
fromAnd {a = True}  {b = False} refl impossible
fromAnd {a = False} {b}         refl impossible

public export
toAnd : a = True -> b = True -> a && Delay b = True
toAnd ra rb = cong2 (&&) ra (cong delay rb)
```

We are now ready to prove the correctness of `Eq` for
`Pair` and `Either`:

```idris
export
EqV a => EqV b => EqV (a,b) where
  eqRefl (a,b) = toAnd (eqRefl a) (eqRefl b)

  eqSym (a1,b1) (a2,b2) = cong2 (&&) (eqSym a1 a2) (cong delay $ eqSym b1 b2)

  eqTrans (a1,b1) (a2,b2) (a3,b3) ab12 ab23 =
    let (a12,b12) = fromAnd ab12
        (a23,b23) = fromAnd ab23
     in toAnd (eqTrans a1 a2 a3 a12 a23) (eqTrans b1 b2 b3 b12 b23)

  neqNotEq (_,_) (_,_)= Refl

export
EqV a => EqV b => EqV (Either a b) where
  eqRefl (Left a)  = eqRefl a
  eqRefl (Right b) = eqRefl b

  eqSym (Left x) (Left y)   = eqSym x y
  eqSym (Left a) (Right b)  = Refl
  eqSym (Right b) (Left a)  = Refl
  eqSym (Right x) (Right y) = eqSym x y

  eqTrans (Left x) (Left y) (Left z) xy yz    = eqTrans x y z xy yz
  eqTrans (Right x) (Right y) (Right z) xy yz = eqTrans x y z xy yz
  eqTrans (Left _) (Right _) _ _ _ impossible
  eqTrans _ (Left _) (Right _) _ _ impossible
  eqTrans (Right _) (Left _) _ _ _ impossible
  eqTrans _ (Right _) (Left _) _ _ impossible

  neqNotEq _ _      = Refl
```

Great, we should be able to do exactly the same thing
for `NP` and `SOP`.

## Verifying `Eq` for `NP` and `SOP`: Take One

Our first approach might be the following (the same
technique was used for the `Ord` instances
in the [first post about generics](Generic1.md)):

```repl
All Eq ts => All EqV ts => EqV (NP ts) where
```

However, this will not work and it took me quite
some time to figure out why. The problem with the declaration above is
that `All Eq ts` and `All EqV ts` might refer
to different instances of `Eq`. In fact, `All Eq ts`
shouldn't even be there. It was a hack because I could
not figure out how to easily extract `All Eq ts`
from `All EqV ts`. Luckily, Idris realized that the two tuples
of interface instances might be completely unrelated:
It refused to accept any implementation for `EqV`'s
propositions. The problem: `EqV` should only be able
to prove the correctness about the `Eq` instance
that comes with itself. That's why we write
`Eq a => EqV a` in our definition of `EqV`. And it should of course
not be able to prove stuff about different, unrelated implementations
of `Eq` without somehow holding a reference to those implementations.
But that is what we are trying to do with the above
type declaration: The `Eq` implementation for `NP`
will come from `All Eq ts`, while we try to implement
`EqV` using the instances from `All EqV ts`, which might
well be completely unrelated to `All Eq ts`.

For `Eq` this might not be a real issue in practice: We typically
only write instances for it once. For other interfaces like
`Semigroup` however, this could be a real problem, since
it is not unusual for a data type to have more than one
valid instance of `Semigroup`.

I got quite frustrated with all of this, since I was sure
my `Eq` implementation for `NP` was correct. So frustrated, in fact,
that I was close to using the big cheating hammer called
`believe_me` just to convince Idris that I was right
and Idris was not. So here's the take home message for
my future self: If Idris refuses to accept a proof it is almost
always right, so stop forcing it to believe otherwise.

## Verifying `Eq` for `NP` and `SOP`: Take Two

The solution seems clear: We must drop our fancy single instance
definitions using `All` and do it the classical way
as in `Data.HVect` from contrib:

```repl
Eq (NP []) where

Eq t => Eq (NP ts) => Eq (NP (t :: ts)) where

EqV (NP []) where

EqV t => EqV (NP ts) => EqV (NP (t :: ts)) where
```

This works, and `EqV` instances can be implemented almost exactly
the same way as for tuples above. However, since I'm using
a similar design in [idris2-sop](https://github.com/stefan-hoeck/idris2-sop)
I changed implementations there as well and soon realized that the
derived `Ord` implementations of some of my example data types
suddenly took ages to typecheck. I quickly verified that
the same was the case for `Data.HVect` from *contrib*, opened an
[issue on idris-lang](https://github.com/idris-lang/Idris2/issues/783) about
this and started looking for a way to get the original fast
compilation times back while at the same time getting rid of the hacky
(and wrong!) way to write interface implementations using `All`.
Eventually, this led to a major rewrite of *idris2-sop*, which
is also why in this post I will have to come up with new versions
of `NP` and `SOP`.

## Adding some Flexibility to `NP`

Before we can write *Verifying Eq for NP: Take Three*, we will
need some more flexibility from `NP` itself: It is time
to go full *idris2-sop* and turn `NP` and `SOP` into
[barbies](https://github.com/jcpetruzza/barbies):

```idris
namespace NP
  public export
  data NP' : (0 k : Type) -> (0 f : k -> Type) -> (0 ks : List k) -> Type where
    Nil  : NP' k f []
    (::) : (v : f t) -> (vs : NP' k f ks) -> NP' k f (t :: ks)

  ||| Type alias for `NP'` with type parameter `k` being implicit.
  public export
  NP : {0 k : Type} -> (0 f : k -> Type) -> (0 ks : List k) -> Type
  NP = NP' k
```

As can be seen: `NP` is no longer indexed over a list of
`Type`s but over an arbitrary list of values. In addition,
it is parameterized over a type constructor `f`.
This allows us to wrap the values in `NP` in different
contexts. There is also function `mapNP`, which allows us
to change contexts:

```idris
public export
mapNP : (fun : forall a . f a -> g a) -> NP f ks -> NP g ks
mapNP fun []        = []
mapNP fun (v :: vs) = fun v :: mapNP fun vs
```

This new flexibility allows us to write a new version of `All`:

```idris
All : (f : k -> Type) -> (ks : List k) -> Type
All f ks = NP f ks
```

So now we can also use `NP` as a heterogeneous list of constraints!
In addition, we can come up with a hinted function for turning
a list of `Ord` implementations into a list of `Eq` instances:

```idris
||| Materializes an implicit value
public export
materialize : (0 c : k -> Type) -> (instance : c v) => c v
materialize _ {instance} = instance

public export %hint
allOrdToAllEq :  {0 ks : List k} -> All (Ord . f) ks -> All (Eq . f) ks
allOrdToAllEq = mapNP (\_ => materialize Eq)
```

Finally, we can have sane `Eq` and `Ord` instances for `NP`:

```idris
public export
(all : All (Eq . f) ks) => Eq (NP' k f ks) where
  (==) {all = []}     [] []               = True
  (==) {all = _ :: _} (v :: vs) (w :: ws) = v == w && vs == ws

public export
(all : All (Ord . f) ks) => Ord (NP' k f ks) where
  compare {all = []}     [] []               = EQ
  compare {all = _ :: _} (v :: vs) (w :: ws) = compare v w <+> compare vs ws
```

Once again, Idris grants us a lot of flexibility. I like the ability to
pattern match on the implicit `all` arguments. Before we continue,
let's just quickly make sure typechecking performs reasonably:

```idris
replicate : Nat -> a -> List a
replicate Z _     = []
replicate (S n) a = a :: replicate n a

testComp : (a,b : NP Maybe $ replicate 10 Int) -> Ordering
testComp = compare
```

This typechecks very quickly on my machine, so all seems
to be fine.
With that out of the way, we are ready to prove the correctness
of `NP`'s `Eq` implementation.

## Verifying `Eq` for `NP`: Take Three

And here it is:

```idris
public export %hint
allEqvToAllEq :  {0 ks : List k} -> All (EqV . f) ks -> All (Eq . f) ks
allEqvToAllEq = mapNP (\_ => materialize Eq)

export
(all : All (EqV . f) ks) => EqV (NP' k f ks) where
  eqRefl {all = []}   []        = Refl
  eqRefl {all = _::_} (v :: vs) = toAnd (eqRefl v) (eqRefl vs)

  eqSym {all = []}     [] [] = Refl
  eqSym {all = _::_} (v :: vs) (w :: ws) =
    cong2 (&&) (eqSym v w) (cong delay $ eqSym vs ws)

  eqTrans {all = []}   [] [] [] Refl Refl = Refl
  eqTrans {all = _::_} (a1 :: as1) (a2 :: as2) (a3 :: as3) o12 o23 =
    let (a12,as12) = fromAnd o12
        (a23,as23) = fromAnd o23
     in toAnd (eqTrans a1 a2 a3 a12 a23) (eqTrans as1 as2 as3 as12 as23)

  neqNotEq _ _      = Refl
```

This is very similar to the `EqV` implementation
for pairs, of course.

## Verifying `Eq` for `SOP`

It is now straightforward to write an implementation of `EqV`
for `SOP`. However, we need another data structure for
wrapping our interface instances in:

```idris
namespace POP
  ||| A product of products used for wrapping constraints for `SOP`.
  public export
  data POP' :  (0 k : Type)
            -> (0 f : k -> Type)
            -> (0 kss : List $ List k)
            -> Type where
    Nil  : POP' k f []
    (::) : (vs : NP' k f ks) -> (vss : POP' k f kss) -> POP' k f (ks :: kss)

||| Type alias for `POP'` with type parameter `k` being implicit.
public export
POP : {0 k : Type} -> (0 f : k -> Type) -> (0 kss : List $ List k) -> Type
POP = POP' k

public export
All2 : (f : k -> Type) -> (kss : List $ List k) -> Type
All2 f kss = POP f kss

public export
mapPOP : (fun : forall a . f a -> g a) -> POP f kss -> POP g kss
mapPOP fun []          = []
mapPOP fun (vs :: vss) = mapNP fun vs :: mapPOP fun vss

public export %hint
allOrdToAllEqPOP :
     {0 ks : List $ List k}
  -> All2 (Ord . f) kss -> All2 (Eq . f) kss
allOrdToAllEqPOP = mapPOP (\_ => materialize Eq)

public export %hint
allEqvToAllEqPOP :
     {0 ks : List $ List k}
  -> All2 (EqV . f) kss -> All2 (Eq . f) kss
allEqvToAllEqPOP = mapPOP (\_ => materialize Eq)
```

And here's `SOP`, our sum of products plus interface implementations:

```idris
public export
data SOP' :  (0 k : Type)
          -> (0 f : k -> Type)
          -> (0 kss : List $ List k)
          -> Type where
  Z : (vs : NP' k f ks)  -> SOP' k f (ks :: kss)
  S : SOP' k f kss -> SOP' k f (ks :: kss)

public export
SOP : {0 k : Type} -> (0 f : k -> Type) -> (0 kss : List (List k)) -> Type
SOP = SOP' k

public export
(all : All2 (Eq . f) kss) => Eq (SOP' k f kss) where
  (==) {all = s::_} (Z vs) (Z ws) = vs == ws
  (==) {all = _::_} (S x)  (S y)  = x  == y
  (==) {all = _::_} _      _      = False

public export
(all : All2 (Ord . f) kss) => Ord (SOP' k f kss) where
  compare {all = _::_} (Z vs) (Z ws) = compare vs ws
  compare {all = _::_} (S x)  (S y)  = compare x y
  compare {all = _::_} (Z _)  (S _)  = LT
  compare {all = _::_} (S _)  (Z _)  = GT
```

We now have the ingredients to prove the correctness of
`SOP`'s `Eq` implementation:

```idris
export
(all : All2 (EqV . f) kss) => EqV (SOP' k f kss) where
  eqRefl {all = _::_} (Z vs) = eqRefl vs
  eqRefl {all = _::_} (S x)  = eqRefl x

  eqSym {all = _::_} (Z vs) (Z ws) = eqSym vs ws
  eqSym {all = _::_} (Z _)  (S _)  = Refl
  eqSym {all = _::_} (S _)  (Z _)  = Refl
  eqSym {all = _::_} (S x)  (S y)  = eqSym x y

  eqTrans {all = _::_} (Z x) (Z y) (Z z) xy yz = eqTrans x y z xy yz
  eqTrans {all = _::_} (S x) (S y) (S z) xy yz = eqTrans x y z xy yz
  eqTrans {all = _::_} (Z _) (S _) _ _ _ impossible
  eqTrans {all = _::_} _ (Z _) (S _) _ _ impossible
  eqTrans {all = _::_} (S _) (Z _) _ _ _ impossible
  eqTrans {all = _::_} _ (S _) (Z _) _ _ impossible

  neqNotEq _ _      = Refl
```

## Why not the original version of `All`?

Now, that we arrived at our goal of having a performant
and provably correct implementation of `Eq` for `SOP`,
I'd like to just quickly explain, why we redefined `All`
when it still looks so similar to the original version.
As a quick reminder, here's how `All` was implemented
in the first post about generics:

```repl
All : (f : Type -> Type) -> (ts : List Type) -> Type
All f [] = ()
All f (t::ts) = (f t, All f ts)
```

The advantage of this representation as nested pairs was that
there was no need to explicitly pattern match on the pair's
structure when implementing `Eq` and `Ord` for `NP` and `SOP`.
However, it was also not possible to implement the following
function

```repl
allOrdToEq : All Ord ts -> All Eq ts
```

without a way to pattern match on `ts` to get an idea
about the underlying structure of `All Ord ts`.
For this, we would have had to include `ts`
as a non-erased argument:

```repl
allOrdToEq : {ts : List Type} -> All Eq ts -> All Ord ts
```

This would have forced us to also have `ts` as a non-erased
argument to our interface implementations (ugly!)
but even then Idris refuses to accept a `%hint` annotation
on `allOrdToEq` with the following error message:
*Can only add hints for concrete return types*.
Going via a well-structured data type resolves all these issues.

## What's next

And that's it for this first part. We are now ready to automatically
derive provably correct interface implementations. That second part will
[follow shortly](Generic7.md).

<!-- vi: filetype=idris2:syntax=markdown
-->
