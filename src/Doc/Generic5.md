## Generics Part 5: Type checked Elaborator Scripts

In this part of the tutorial we try out at a new technique to get back
some of our beloved type safety when writing elaborator scripts.

```idris
module Doc.Generic5

import public Language.Reflection.Derive
import Doc.Generic1

%language ElabReflection
```

### Properly Typed Default Implementations

When we look back at [Generics Part 4](Generic4.md), 
we find that the writing of `Eq'` and `Ord'` forced us to implement these
completely in the untyped world of `TTImp`, simply because we did not
have access to the corresponding record constructors of
`Eq` and `Ord`. But it is actually very easy to get that
constructor back as a properly typed function by using
function `check` from `Language.Reflection`:

```idris
mkEq' : (eq : a -> a -> Bool) -> (neq : a -> a -> Bool) -> Eq a
mkEq' = %runElab check (var $ singleCon "Eq")
```

So, `check` tries to retype an untyped `TTImp` value during
elaboration reflection. Needless to say, we get a type error
if the types do not match. The following, for instance, does not
compile:

```
mkEq' : (eq : a -> a -> Bool) -> Eq a
mkEq' = %runElab check (var $ singleCon "Eq")
```

Now that we have access to `Eq`'s constructor, we can get quite a bit
of type safety back:

```idris
mkEq : (eq : a -> a -> Bool) -> Eq a
mkEq eq = mkEq' eq (\a,b => not $ eq a b)

Eq' : DeriveUtil -> InterfaceImpl
Eq' g = MkInterfaceImpl "Eq" Public `(mkEq genEq) (implementationType `(Eq) g)
```

This time, we used the utilities from `Language.Reflection.Derive`. 
They are very similar in functionality to the ones developed in
[Generics Part 4](Generic4.md). This
approach is even more useful when deriving `Ord`: In our previous
version we had to manually pass the `Eq` instance to the `Ord`
constructor forcing us to get access to its implementation function
by means of `implName`. This is now no longer necessary:

```idris
mkOrd' :  (1 _ : Eq a)
      -> (compare : a -> a -> Ordering)
      -> (lt : a -> a -> Bool)
      -> (gt : a -> a -> Bool)
      -> (leq : a -> a -> Bool)
      -> (geq : a -> a -> Bool)
      -> (min : a -> a -> a)
      -> (max : a -> a -> a)
      -> Ord a
mkOrd' = %runElab check (var $ singleCon "Ord")

mkOrd : (1 prf : Eq a) => (comp : a -> a -> Ordering) -> Ord a
mkOrd comp = mkOrd' prf
                    comp
                    (\a,b => comp a b == LT)
                    (\a,b => comp a b == GT)
                    (\a,b => comp a b /= GT)
                    (\a,b => comp a b /= LT)
                    (\a,b => if comp a b == GT then a else b)
                    (\a,b => if comp a b == LT then a else b)

Ord' : DeriveUtil -> InterfaceImpl
Ord' g = MkInterfaceImpl "Ord" Public `(mkOrd genCompare)
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

ordTest : Foo (the Int 12) <= Bar "bar" = True
ordTest = Refl
```

### Conclusion

In this very short tutorial we learned that
function `check` is useful whenever we try to implement
a function using elaborator reflection whose type is already known at compile time.
This was not the case for automatically derived interface implementations
whose full type had to be put together from the correspoding
data type's constructors, type parameters, and constructor
arguments. It was, however, possible for functions to create
interface record values whose type we already knew but whose
strangely named constructors we could not use directly in our code.
