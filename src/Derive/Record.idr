module Derive.Record

import Derive.Eq
import Derive.Ord
import Derive.Show
import Language.Reflection.Derive
import public Data.DPair

||| Proof that the given data type only has a single constructor.
public export
data Record : TypeInfo -> Type where
  IsRecord : Record (MkTypeInfo n k as [c])

||| Checks if the given data type only has a single constructor.
public export
isRecord : (t : TypeInfo) -> Res (Record t)
isRecord (MkTypeInfo _ _ _ [_]) = Right IsRecord
isRecord _                      = Left "Not exactly one constructor"

public export
getConstructor :
     (t : TypeInfo)
  -> {auto 0 prf : Record t}
  -> Con t.arty t.args
getConstructor (MkTypeInfo _ _ _ [c]) {prf = IsRecord} = c

public export %inline
Elaborateable (Subset TypeInfo Record) where
  find_ = refine isRecord

public export
0 ParamRecord : Type
ParamRecord = Subset ParamTypeInfo (Record . info)

public export %inline
Elaborateable ParamRecord where
  find_ = refine (\t => isRecord t.info)

||| Given a name of a parameterized record type plus a list of
||| interface generation functions, tries
||| to implement these interfaces automatically using
||| elaborator reflection.
export %inline
deriveRecord :
     Elaboration m
  => Name
  -> List (List Name -> ParamRecord -> List TopLevel)
  -> m ()
deriveRecord n = deriveGeneral [n]

||| Generate declarations and implementations for `Eq` for a given record type.
export %inline
Eq : List Name -> ParamRecord -> List TopLevel
Eq nms = Eq nms . fst

||| Generate declarations and implementations for `Ord` for a given record type.
export %inline
Ord : List Name -> ParamRecord -> List TopLevel
Ord nms = Ord nms . fst

||| Generate declarations and implementations for `Show` for a given record type.
export %inline
Show : List Name -> ParamRecord -> List TopLevel
Show nms = Show nms . fst
