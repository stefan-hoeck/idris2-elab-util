## Generics Part 4

We would now like to clean up the syntax for deriving
generic instances a bit. There is quite a bit of redundant
work going on, so we have the chance to reduce some code
duplication.

```idris
module Doc.Generic4

import public Language.Reflection.Pretty
import public Language.Reflection.Syntax
import public Language.Reflection.Types
import Doc.Generic1
import Doc.Generic3

%language ElabReflection
```

### An Intermediary Utility Type for Generic Deriving

```idris
public export
record GenericUtil where
  constructor MkGenericUtil
  typeInfo        : ParamTypeInfo
  appliedType     : TTImp 
  paramNames      : List Name
  typesWithParams : List TTImp

genericUtil : ParamTypeInfo -> GenericUtil
genericUtil ti = let pNames = map fst $ params ti
                     appTpe = appNames (name ti) pNames
                     twps   = ti.cons >>= hasParamTypes
                  in MkGenericUtil ti appTpe pNames twps
```

```idris
export
record Derivable where
  constructor MkDerivable
  interfaceName : String
  impl          : TTImp
  type          : TTImp

export
implName : GenericUtil -> String -> Name
implName g interfaceName =  UN $ "impl" ++ interfaceName
                                        ++ nameStr g.typeInfo.name

private
deriveDerivable : GenericUtil -> Derivable -> Elab ()
deriveDerivable g d = let function = implName g d.interfaceName
                       in declare [ interfaceHint Public function d.type
                                  , def function [ var function .= d.impl ] ]

export
derive : Name -> List (GenericUtil -> Derivable) -> Elab ()
derive name fs = do g <- genericUtil <$> getParamInfo' name
                    traverse_ (\f => deriveDerivable g (f g)) fs

```

```idris
private
mkGeneric : Name
mkGeneric = singleCon "Generic"

private
fromClause : (Int,ParamCon) -> Clause
fromClause (n,MkParamCon nm args) =
  let names = map (nameStr . name) args
   in bindAll nm names .= mkSOP n (map varStr names)

private
toClause : (Int,ParamCon) -> Clause
toClause (n,MkParamCon nm args) =
  let names = map (nameStr . name) args
   in mkSOP n (map bindVar names) .= appAll nm (map varStr names)
                                   

export
Generic' : GenericUtil -> Derivable
Generic' g =
  let cde     = mkCode g.typeInfo

      iCons    = zipWithIndex (g.typeInfo.cons)
      genType  = `(Generic) .$ g.appliedType .$ cde
      funType  = piAllImplicit  genType g.paramNames
      x        = lambdaArg "x"

      from    = x .=> iCase (var "x") implicitFalse (map fromClause iCons)
      to      = x .=> iCase (var "x") implicitFalse (map toClause iCons)
      impl    = appAll mkGeneric [from,to]

   in MkDerivable "Generic" impl funType

private
mkEq : TTImp
mkEq = var (singleCon "Eq") .$ `(genEq) .$ `(\a,b => not (a == b))

export
implementationType : TTImp -> GenericUtil -> TTImp
implementationType iface (MkGenericUtil _ appTp names typesWithParams) =
  let appIface = iface .$ appTp
      autoArgs = piAllAuto appIface $ map (iface .$) typesWithParams
   in piAllImplicit autoArgs names

export
Eq' : GenericUtil -> Derivable
Eq' g = MkDerivable "Eq" mkEq (implementationType `(Eq) g)

private
mkOrd : Name
mkOrd = singleCon "Ord"

private
ordFunctions : List TTImp
ordFunctions = [ `(genCompare)
               , `(\a,b => compare a b == LT)
               , `(\a,b => compare a b == GT)
               , `(\a,b => compare a b /= GT)
               , `(\a,b => compare a b /= LT)
               , `(\a,b => if compare a b == GT then a else b)
               , `(\a,b => if compare a b == LT then a else b)
               ]

export
Ord' : GenericUtil -> Derivable
Ord' g = let eq   = var $ implName g "Eq"
             impl = appAll mkOrd (eq :: ordFunctions)
          in MkDerivable "Ord" impl (implementationType `(Ord) g)
```

Now, lets put our new utilities to work. Below, we derive
`Generic`, `Eq` and `Ord` implementations for all types
from `Language.Reflection.TT` and `Language.Reflection.TTImp`.

```idris
%runElab (derive "FC"         [Generic', Eq', Ord'])
%runElab (derive "NameType"   [Generic', Eq', Ord'])
%runElab (derive "Constant"   [Generic', Eq', Ord'])
%runElab (derive "Namespace"  [Generic', Eq', Ord'])
%runElab (derive "Name"       [Generic', Eq', Ord'])
%runElab (derive "Count"      [Generic', Eq', Ord'])
%runElab (derive "LazyReason" [Generic', Eq', Ord'])
%runElab (derive "PiInfo"     [Generic', Eq', Ord'])
%runElab (derive "BindMode"   [Generic', Eq', Ord'])
%runElab (derive "UseSide"    [Generic', Eq', Ord'])
%runElab (derive "DotReason"  [Generic', Eq', Ord'])
%runElab (derive "Visibility" [Generic', Eq', Ord'])
%runElab (derive "TotalReq"   [Generic', Eq', Ord'])
%runElab (derive "DataOpt"    [Generic', Eq', Ord'])
```

It is not possible, to use this method in a mutual
block. Therefore, we have to write a tiny bit
of boilerplate for `Eq` and `Ord` instances
of `TTImp` and friends.

```idris
%runElab (derive "TTImp"        [Generic'])
%runElab (derive "IField"       [Generic'])
%runElab (derive "IFieldUpdate" [Generic'])
%runElab (derive "AltType"      [Generic'])
%runElab (derive "FnOpt"        [Generic'])
%runElab (derive "ITy"          [Generic'])
%runElab (derive "Data"         [Generic'])
%runElab (derive "Record"       [Generic'])
%runElab (derive "Clause"       [Generic'])
%runElab (derive "Decl"         [Generic'])

mutual
  export
  Eq TTImp where (==) = genEq

  export
  Eq IField where (==) = genEq

  export
  Eq IFieldUpdate where (==) = genEq

  export
  Eq AltType where (==) = genEq

  export
  Eq FnOpt where (==) = genEq

  export
  Eq ITy where (==) = genEq

  export
  Eq Data where (==) = genEq

  export
  Eq Record where (==) = genEq

  export
  Eq Clause where (==) = genEq

  export
  Eq Decl where (==) = genEq

  export
  Ord TTImp where compare = genCompare

  export
  Ord IField where compare = genCompare

  export
  Ord IFieldUpdate where compare = genCompare

  export
  Ord AltType where compare = genCompare

  export
  Ord FnOpt where compare = genCompare

  export
  Ord ITy where compare = genCompare

  export
  Ord Data where compare = genCompare

  export
  Ord Record where compare = genCompare

  export
  Ord Clause where compare = genCompare

  export
  Ord Decl where compare = genCompare
```

