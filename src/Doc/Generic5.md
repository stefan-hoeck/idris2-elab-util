# Type checked Elaborator Scripts

In this part of the tutorial we try out a new technique to get back
some of our beloved type safety when writing elaborator scripts.

```idris
module Doc.Generic5

import public Language.Reflection.Derive
import Doc.Generic1

%hide Language.Reflection.Derive.mkEq
%hide Language.Reflection.Derive.mkOrd

%language ElabReflection
```

## Properly Typed Default Implementations

When we look back at [Generics Part 4](Generic4.md),
we find that the writing of `Eq'` and `Ord'` forced us to implement these
completely in the untyped world of `TTImp`, simply because we did not
have access to the corresponding record constructors of
`Eq` and `Ord`. But it is actually very easy to get those
constructors back as a properly typed functions by using
function `check` from `Language.Reflection`:

```idris
mkEq' : (eq : a -> a -> Bool) -> (neq : a -> a -> Bool) -> Eq a
mkEq' = %runElab check (var $ singleCon "Eq")
```

Note that strictly speaking, the above is no longer necessary,
as `Eq` has been given a properly named constructor. I still
leave this as a usage example of `check`.

So, `check` tries to retype an untyped `TTImp` value during
elaboration reflection. Needless to say, we get a type error
if the types do not match. The following, for instance, does not
compile:

```repl
mkEq' : (eq : a -> a -> Bool) -> Eq a
mkEq' = %runElab check (var $ singleCon "Eq")
```

Now that we have access to `Eq`'s constructor, we can get quite a bit
of type safety back:

```idris
mkEq : (eq : a -> a -> Bool) -> Eq a
mkEq eq = mkEq' eq (\a,b => not $ eq a b)

Eq' : DeriveUtil -> InterfaceImpl
Eq' g = MkInterfaceImpl "Eq" Public [] `(mkEq genEq) (implementationType `(Eq) g)
```

This time, we used utilities from `Language.Reflection.Derive`.
They are very similar in functionality to the ones we developed in
[Generics Part 4](Generic4.md). This
approach is even more useful when deriving `Ord`: In our previous
version we had to manually pass the `Eq` instance to the `Ord`
constructor, forcing us to get access to its implementation function
by means of `implName`. This is no longer necessary:

```idris
mkOrd' :  Eq a
       => (compare : a -> a -> Ordering)
       -> (lt : a -> a -> Bool)
       -> (gt : a -> a -> Bool)
       -> (leq : a -> a -> Bool)
       -> (geq : a -> a -> Bool)
       -> (max : a -> a -> a)
       -> (min : a -> a -> a)
       -> Ord a
mkOrd' = %runElab check (var $ singleCon "Ord")

mkOrd : Eq a => (comp : a -> a -> Ordering) -> Ord a
mkOrd comp = mkOrd' comp
                    (\a,b => comp a b == LT)
                    (\a,b => comp a b == GT)
                    (\a,b => comp a b /= GT)
                    (\a,b => comp a b /= LT)
                    (\a,b => if comp a b == GT then a else b)
                    (\a,b => if comp a b == LT then a else b)

Ord' : DeriveUtil -> InterfaceImpl
Ord' g = MkInterfaceImpl "Ord" Public [] `(mkOrd genCompare)
                                         (implementationType `(Ord) g)
```

We quickly test if it works:

```idris
data Test a = Foo a | Bar String

Generic (Test a) [[a],[String]] where
  from (Foo a) = Z [a]
  from (Bar s) = S $ Z [s]

  to (Z [a])     = Foo a
  to (S $ Z [s]) = Bar s

%runElab (derive "Test" [Eq',Ord'])

eqTest : let v = Foo (the Int 12) in v == v = True
eqTest = Refl

neqTest : let v = Foo (the Int 12) in v /= v = False
neqTest = Refl
```

For `Ord` we need to be more thorough and make sure we
did not mix up the order of functions in the constructor:

```idris
compareTest1 : compare (the (Test Int) (Foo 12)) (Bar "bar") = LT
compareTest1 = Refl

compareTest2 : compare (the (Test Int) (Foo 12)) (Foo 1) = GT
compareTest2 = Refl

compareTest3 : compare (the (Test Int) (Foo 12)) (Foo 12) = EQ
compareTest3 = Refl

ltTest1 : the (Test Int) (Foo 12) < Bar "bar" = True
ltTest1 = Refl

ltTest2 : the (Test Int) (Foo 12) < Foo 12 = False
ltTest2 = Refl

gtTest1 : the (Test Int) (Foo 12) > Foo 0 = True
gtTest1 = Refl

gtTest2 : the (Test Int) (Foo 12) > Foo 12 = False
gtTest2 = Refl

leqTest1 : the (Test Int) (Foo 12) <= Bar "bar" = True
leqTest1 = Refl

leqTest2 : the (Test Int) (Bar "bar") <= Bar "bar" = True
leqTest2 = Refl

geqTest1 : the (Test Int) (Foo 12) >= Foo 1 = True
geqTest1 = Refl

geqTest2 : the (Test Int) (Bar "bar") >= Bar "bar" = True
geqTest2 = Refl

minTest : min (the (Test Int) (Foo 2)) (Foo 3) = Foo 2
minTest = Refl

maxTest : max (the (Test Int) (Foo 2)) (Foo 3) = Foo 3
maxTest = Refl
```

## Conclusion

In this very short tutorial we learned that the
function `check` is useful whenever we try to implement
a function using elaborator reflection whose type is already known at compile time.
This was not the case for automatically derived interface implementations
whose full type had to be put together from the corresponding
data type's name and type parameters.
It was, however, possible for record constructors
whose types we already knew but whose names we had
to look up using elaborator reflection.
