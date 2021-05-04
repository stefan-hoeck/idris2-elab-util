## Deriving `Generic` for Parameterized Data Types

After our analysis in [part 2](Generic2.md), we should now have
the ingredients to derive `Generic` instances for parameterized
types.

```idris
module Doc.Generic3

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import Doc.Generic1

%language ElabReflection

```

Most of the utility functions are almost the same as
in module `Doc.Generic1`.

```idris
export
paramConNames : ParamCon -> ConNames
paramConNames (MkParamCon con args) = let ns   = map (nameStr . name) args
                                          vars = map varStr ns
                                       in (con, ns, vars)

export
mkCode : ParamTypeInfo -> TTImp
mkCode = listOf . map (listOf . map tpe . explicitArgs) . cons
```

The implementation of `genericDecl`, however, requires an
additional step: In the definition of the function type,
we must include the type parameters as implicit arguments.
Utility function `piAllImplicit` helps with this part.

```idris
export
genericDecl : ParamTypeInfo -> List Decl
genericDecl ti =
  let names    = zipWithIndex (map paramConNames ti.cons)
      function   = UN $ "implGeneric" ++ camelCase (name ti)
      paramNames = map fst $ params ti

      -- Applies parameters to type constructor, i.e. `Either a b`
      appType   = appNames (name ti) paramNames
      genType  = `(Generic) .$ appType .$ mkCode ti

      -- Prefixes function type with implicit arguments for
      -- type parameters:
      -- `{0 a : _} -> {0 b : _} -> Generic (Either a b) [[a],[b]]`
      funType  = piAllImplicit genType paramNames

      x       = lambdaArg "x"
      varX    = var "x"
      from    = x .=> iCase varX implicitFalse (map fromClause names)
      to      = x .=> iCase varX implicitFalse (toClauses names)

   in [ interfaceHint Public function funType
      , def function [ var function .= appAll mkGeneric [from,to] ] ]

export
deriveGeneric : Name -> Elab ()
deriveGeneric name = getParamInfo' name >>= declare . genericDecl
```

OK, let's give this a spin:

```idris
private
data Tree a = Leaf a | Branch (List (Tree a))

%runElab (deriveGeneric "Tree")

private
Eq a => Eq (Tree a) where (==) = genEq

private
Ord a => Ord (Tree a) where compare = genCompare

private
treeTest1 : (Leaf "foo" == Leaf "foo") = True
treeTest1 = Refl

private
treeTest2 : (Branch [Leaf "bar"] == Branch [Leaf "bar"]) = True
treeTest2 = Refl

private
treeTest3 : (Branch [Leaf "bar"] == Branch [Leaf "foo"]) = False
treeTest3 = Refl

private
treeTest4 : (Leaf "bar" < Leaf "foo") = True
treeTest4 = Refl

private
treeTest5 : (Leaf "foo" > Leaf "foo") = False
treeTest5 = Refl
```

And something a bit more involved:

```idris
private
data Crazy : (n : Nat) -> (a : Type) -> (f : Type -> Type) -> Type where
  CrazyA : Vect n a -> f a -> Crazy n a f
  CrazyB : List (g b) -> Crazy n b g
  CrazyC : Crazy foo bar baz

%runElab (deriveGeneric "Crazy")

private
(Eq a, Eq (f a)) => Eq (Crazy n a f) where (==) = genEq

private
(Ord a, Ord (f a)) => Ord (Crazy n a f) where compare = genCompare

private
crazyTest1 : (CrazyA {f = Maybe} [1] (Just 7) == CrazyA [1] (Just 7)) = True
crazyTest1 = Refl

private
crazyTest2 : (the (Crazy 2 Int List) CrazyC == CrazyB [[12]]) = False
crazyTest2 = Refl
```

### What's next

This was pretty straight forward. In the [next post](Generic4.md) I'll
have a look at
automating the writing of `Eq` and `Ord` instances.
