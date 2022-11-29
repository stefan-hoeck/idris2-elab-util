module Derive.Record

import public Data.DPair
import Language.Reflection.Derive

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
0 ParamRecord : ParamTypeInfo -> Type
ParamRecord t = Record t.info

public export %inline
Elaborateable (Subset ParamTypeInfo ParamRecord) where
  find_ = refine (\t => isRecord t.info)

||| Given a name of a parameterized record type plus a list of
||| interface generation functions, tries
||| to implement these interfaces automatically using
||| elaborator reflection.
export %inline
deriveRecord :
     Elaboration m
  => Name
  -> List (List Name -> Subset ParamTypeInfo ParamRecord -> List TopLevel)
  -> m ()
deriveRecord n = deriveGeneral [n]
