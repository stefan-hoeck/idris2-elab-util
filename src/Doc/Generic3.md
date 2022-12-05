# Deriving `Generic` for Parameterized Data Types

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
in module `Doc.Generic1`. However, we must make sure we are only
going to bind explicit constructor arguments.

```idris
export
paramConNames : ParamCon n -> ConNames
paramConNames c =
  let ns   := toList $ freshNames "x" (count isExplicit c.args)
      vars := map var ns
   in (c.name, map nameStr ns, vars)

export
mkCode : (p : ParamTypeInfo) -> TTImp
mkCode p = listOf $ map (\c => listOf $ explicits c.args) p.cons
  where explicits : Vect n (ConArg p.numParams) -> List TTImp
        explicits [] = []
        explicits (CArg _ _ ExplicitArg t :: as) =
          ttimp p.paramNames t :: explicits as
        explicits (_ :: as) = explicits as
```

Note, that in order to convert the argument types back to `TTImp`,
we need a vector of parameter names of the correct length. This is to make
sure we use the same parameter names throughout the generation of the
desired declarations.

The implementation of `genericDecl`, however, requires an
additional step: In the definition of the function type,
we must include the type parameters as implicit arguments.
The utility function `piAllImplicit` helps with this part.

```idris
export
genericDecl : (p : ParamTypeInfo) -> List Decl
genericDecl p =
  let names    = zipWithIndex (map paramConNames p.cons)
      function   = UN . Basic $ "implGeneric" ++ camelCase p.info.name

      -- Applies parameters to type constructor, i.e. `Either a b`
      appType  = p.applied
      genType  = `(Generic) .$ appType .$ mkCode p

      -- Prefixes function type with implicit arguments for
      -- type parameters:
      -- `{0 a : _} -> {0 b : _} -> Generic (Either a b) [[a],[b]]`
      funType  = piAll genType p.implicits

      x       = lambdaArg {a = Name} "x"
      varX    = var "x"
      from    = x .=> iCase varX implicitFalse (map fromClause names)
      to      = x .=> iCase varX implicitFalse (toClauses names)

   in [ interfaceHint Public function funType
      , def function [ var function .= appAll "MkGeneric" [from,to] ] ]

export
deriveGeneric : Name -> Elab ()
deriveGeneric name = do
  p <- getParamInfo' name
  declare $ genericDecl p
```

OK, let's give this a spin:

```idris
private
data Tree a = Leaf a | Branch (List (Tree a))

%runElab (deriveGeneric "Tree")

private
Eq a => Eq (Tree a) where (==) = assert_total genEq

private
Ord a => Ord (Tree a) where compare = assert_total genCompare

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

## What's next

This was pretty straight forward. In the [next post](Generic4.md) I'll
have a look at
automating the writing of `Eq` and `Ord` instances.
