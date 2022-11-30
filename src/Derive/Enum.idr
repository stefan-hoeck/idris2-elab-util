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

public export
0 Enum : Type
Enum = Subset TypeInfo RuntimeEnum


||| Tries to convert a type info to an runtime enum.
public export
runtimeEnum : (t : TypeInfo) -> Res (RuntimeEnum t)
runtimeEnum (MkTypeInfo _ _ _ cs) = IsRuntimeEnum <$> runtimeConsts cs

public export %inline
Elaborateable Enum where
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
Eq : List Name -> Enum -> List TopLevel
Eq nms (Element t _) =
  let ns := freshNames "par" t.arty
      nm := implName t "Eq"
      ci := var $ funName t "conIndex"
      cl := var nm .= `(mkEq $ \x,y => ~(ci) x == ~(ci) y)
   in ConIndex nms t ++
      [ TL (implClaim nm (ifaceClaimType "Eq" t ns)) (def nm [cl]) ]

export
Ord : List Name -> Enum -> List TopLevel
Ord nms (Element t _) =
  let ns := freshNames "par" t.arty
      nm := implName t "Ord"
      ci := var $ funName t "conIndex"
      cl := var nm .= `(mkOrd $ \x,y => compare (~(ci) x) (~(ci) y))
   in [ TL (implClaim nm (ifaceClaimType "Ord" t ns)) (def nm [cl]) ]

export
Show : List Name -> Enum -> List TopLevel
Show nms (Element t _) =
  let ns   := freshNames "par" t.arty
      impl := implName t "Show"
      fun  := funName t "showPrec"
      tpe  := generalShowType (implicits ns) $ appArgs t.name ns
      clm := public' fun tpe
   in [ TL clm (showDef [] fun t)
      , TL (implClaim impl (ifaceClaimType "Show" t ns)) (showImplDef fun impl)
      ]

||| Given a name of an enum type plus a list of
||| interface generation functions, tries
||| to implement these interfaces automatically using
||| elaborator reflection.
export %inline
deriveEnum :
     Elaboration m
  => Name
  -> List (List Name -> Enum -> List TopLevel)
  -> m ()
deriveEnum n = deriveGeneral [n]
