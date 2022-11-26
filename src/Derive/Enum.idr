module Derive.Enum

import public Data.DPair
import public Data.List.Quantifiers
import public Data.Vect.Quantifiers
import public Derive.Eq
import public Derive.Ord
import public Derive.Show

%default total

--------------------------------------------------------------------------------
--          Runtime Enum
--------------------------------------------------------------------------------

public export
data ErasedArg : Arg -> Type where
  IsErasedArg : ErasedArg (MkArg M0 p n t)

public export
0 ErasedArgs : Vect n Arg -> Type
ErasedArgs = All ErasedArg

||| Checks if all data constructors in the given list are
||| constants.
public export
erasedArgs : (as : Vect n Arg) -> Res (ErasedArgs as)
erasedArgs []                     = Right []
erasedArgs (MkArg M0 p n        t :: as) = (IsErasedArg ::) <$> erasedArgs as
erasedArgs (MkArg _  _ (Just n) t :: as) = Left "argument \{n} is not erased"
erasedArgs (MkArg _  _ Nothing  t :: as) =
  Left "argument \{show t} is not erased"

||| Proof that the given data constructor is a constant at runtime,
||| that is, it has only erased arguments.
public export
data RuntimeConst : (c : Con n vs) -> Type where
  IsRuntimeConst : {c : Con n vs} -> ErasedArgs c.args -> RuntimeConst c

||| Checks if all data constructors in the given list are
||| constants at runtim.
public export
runtimeConsts : (cs : List (Con n bs)) -> Res (All RuntimeConst cs)
runtimeConsts []                        = Right []
runtimeConsts (MkCon nm arty args tpe :: xs) =
  let Right p  := erasedArgs args  | Left err => Left err
      Right ps := runtimeConsts xs | Left err => Left err
   in Right $ IsRuntimeConst p :: ps

||| Proof that the given data type is an enum at runtime,
||| that is, it has only constructors with erased arguments.
public export
data RuntimeEnum : (i : TypeInfo) -> Type where
  IsRuntimeEnum : {i : TypeInfo} -> All RuntimeConst i.cons -> RuntimeEnum i

||| Tries to convert a type info to an runtime enum.
public export
runtimeEnum : (t : TypeInfo) -> Res (RuntimeEnum t)
runtimeEnum (MkTypeInfo _ _ _ cs) = IsRuntimeEnum <$> runtimeConsts cs

public export %inline
Elaborateable (Subset TypeInfo RuntimeEnum) where
  find_ = refine runtimeEnum

--------------------------------------------------------------------------------
--          Derive Enum
--------------------------------------------------------------------------------

export
ifaceClaimType :
     Name
  -> (t : TypeInfo)
  -> Vect t.arty Name
  -> {auto 0 _ : RuntimeEnum t}
  -> TTImp
ifaceClaimType n t ns = piAll (var n .$ appArgs t.name ns) (implicits ns)

export
eqTL :
     (t : TypeInfo)
  -> Vect t.arty Name
  -> {auto 0 _ : RuntimeEnum t}
  -> TopLevel
eqTL t ns =
  let nm  := t.eqName
      ci  := var $ t.conIndexName
   in TL
        (implClaim nm (ifaceClaimType "Eq" t ns))
        (def nm [var nm .= `(mkEq $ \x,y => ~(ci) x == ~(ci) y)])

export
ordTL :
     (t : TypeInfo)
  -> Vect t.arty Name
  -> {auto 0 _ : RuntimeEnum t}
  -> TopLevel
ordTL t ns =
  let nm := t.ordName
      ci := var $ t.conIndexName
      cl := var nm .= `(mkOrd $ \x,y => compare (~(ci) x) (~(ci) y))
   in TL (implClaim nm (ifaceClaimType "Ord" t ns)) (def nm [cl])

export
showTL :
     (t : TypeInfo)
  -> Vect t.arty Name
  -> {auto 0 _ : RuntimeEnum t}
  -> List TopLevel
showTL t ns =
  let nm  := t.showImplName
      tpe := generalShowType (implicits ns) $ appArgs t.name ns
      clm := public' t.showName tpe
   in [ TL clm (showDef [] t.showName t)
      , TL (implClaim nm (ifaceClaimType "Show" t ns)) (showImplDef t)
      ]

export
Enum : List Name -> Subset TypeInfo RuntimeEnum -> List TopLevel
Enum nms (Element t _) =
  let ns := freshNames "par" t.arty
   in ConIndex nms t ++ [eqTL t ns, ordTL t ns] ++ showTL t ns
