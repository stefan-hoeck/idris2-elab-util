## Generics Part 4

We would now like to clean up the syntax for deriving
generic instances a bit. There is quite a bit redundant
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
  typeInfo    : ParamTypeInfo
  appliedType : TTImp 
  paramNames  : List Name

genericUtil : ParamTypeInfo -> GenericUtil
genericUtil ti = let pNames = map fst $ params ti
                     appTpe = appAll (name ti) pNames
                  in MkGenericUtil ti appTpe pNames
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
                                        ++ unnamespaced g.typeInfo.name

private
deriveDerivable : GenericUtil -> Derivable -> Elab ()
deriveDerivable g d = let function = implName g d.interfaceName
                       in declare [ interfaceHint Public function d.type
                                  , def function [ var function .= d.impl ] ]

export
derive : Name -> List (GenericUtil -> Derivable) -> Elab ()
derive name fs = do g <- genericUtil <$> getParamInfo' name
                    traverse_ (\f => deriveDerivable g (f g)) fs

export
derive' : Name -> List (ParamTypeInfo -> List Decl) -> Elab ()
derive' name fs = do g <- genericUtil <$> getParamInfo' name
                     traverse_ (\f => declare (f g.typeInfo)) fs
```

```idris
private
mkGeneric : TTImp
mkGeneric = appAll (singleCon "Generic") [fromImpl, toImpl]

export
Generic' : GenericUtil -> Derivable
Generic' g =
  let cde = mkCode g.typeInfo

      genType  = `(Generic) .$ g.appliedType .$ cde
      funType  = piAllImplicit genType g.paramNames

      impl  = local [ private' fromImpl $ arg g.appliedType .-> `(SOP) .$ cde
                    , def fromImpl (mkFrom g.typeInfo)

                    , private' toImpl $ arg (`(SOP) .$ cde) .-> g.appliedType
                    , def toImpl (mkTo g.typeInfo)
                    ] mkGeneric

   in MkDerivable "Generic" impl funType

private
mkEq : TTImp
mkEq = var (singleCon "Eq") .$ `(genEq) .$ `(\a,b => not (a == b))

export
Eq' : GenericUtil -> Derivable
Eq' g = let funType  = piAllImplicit (`(Eq) .$ g.appliedType) g.paramNames
         in MkDerivable "Eq" mkEq funType

private
mkOrd : Name
mkOrd = singleCon "Ord"

export
Ord' : GenericUtil -> Derivable
Ord' g =
  let tpe       = g.appliedType
      funType   = piAllImplicit (`(Ord) .$ tpe) g.paramNames
      eq        = var $ implName g "Eq"

      comp = `(genCompare)
      lt   = `(\a,b => compare a b == LT)
      gt   = `(\a,b => compare a b == GT)
      leq  = `(\a,b => compare a b /= GT)
      geq  = `(\a,b => compare a b /= LT)
      max  = `(\a,b => if compare a b == GT then a else b)
      min  = `(\a,b => if compare a b == LT then a else b)

      impl  = var mkOrd .$ eq .$ comp .$ lt .$ gt .$ leq .$ geq .$ max .$ min
   in MkDerivable "Ord" impl funType
```

```idris
%runElab (derive "NameType" [Generic',Eq',Ord'])
%runElab (derive "Constant" [Generic',Eq',Ord'])
%runElab (derive "Namespace" [Generic',Eq',Ord'])
%runElab (derive "Name" [Generic',Eq',Ord'])
%runElab (derive "Count" [Generic',Eq',Ord'])
%runElab (derive "LazyReason" [Generic',Eq',Ord'])
%runElab (derive "PiInfo" [Generic'])
%runElab (derive "BindMode" [Generic',Eq',Ord'])
%runElab (derive "UseSide" [Generic',Eq',Ord'])
%runElab (derive "DotReason" [Generic',Eq',Ord'])
```

