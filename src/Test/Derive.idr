module Test.Derive

import Derive.Prelude

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Enum
--------------------------------------------------------------------------------

public export
data Elem =
    H                                                                                  | He
  | Li | Be                                                   | B  | C  | N  | O  | F  | Ne
  | Na | Mg                                                   | Al | Si | P  | S  | Cl | Ar
  | K  | Ca | Sc | Ti | V  | Cr | Mn | Fe | Co | Ni | Cu | Zn | Ga | Ge | As | Se | Br | Kr
  | Rb | Sr | Y  | Zr | Nb | Mo | Tc | Ru | Rh | Pd | Ag | Cd | In | Sn | Sb | Te | I  | Xe
  | Cs | Ba | La
            | Ce | Pr | Nd | Pm | Sm | Eu | Gd
            | Tb | Dy | Ho | Er | Tm | Yb | Lu
                 | Hf | Ta | W  | Re | Os | Ir | Pt | Au | Hg | Tl | Pb | Bi | Po | At | Rn
  | Fr | Ra | Ac
            | Th | Pa | U  | Np | Pu | Am | Cm
            | Bk | Cf | Es | Fm | Md | No | Lr
                 | Rf | Db | Sg | Bh | Hs | Mt | Ds | Rg | Cn | Nh | Fl | Mc | Lv | Ts | Og

%runElab deriveGeneral ["Elem"] [Enum]

--------------------------------------------------------------------------------
--          Plain
--------------------------------------------------------------------------------

data Error : Type where
  NotAnInteger : (p : String) -> Error
  EmptyString  : Error
  NotABool     : String -> List String -> Error

%runElab derive "Error" [Show, Eq, Ord]

record Test where
  constructor MkTest
  foo : Nat
  bar : String

%runElab derive "Test" [Show, Eq, Ord]

--------------------------------------------------------------------------------
--          Lazy
--------------------------------------------------------------------------------

record LAZY (a : Type) where
  constructor MkLAZY
  wrapped : Lazy a

%runElab derive "LAZY" [Show, Eq, Ord]

--------------------------------------------------------------------------------
--          Phantom
--------------------------------------------------------------------------------

record Constant (a, b : Type) where
  constructor MkConstant
  runConstant : a

%runElab derive "Constant"  [Show,Eq,Ord]

--------------------------------------------------------------------------------
--          Barbie
--------------------------------------------------------------------------------

record Barbie a b (f : Type -> Type) where
  constructor MkBarbie
  id   : f a
  name : f b
  age  : f Nat

%runElab derive "Barbie" [Show, Eq, Ord]

test : Barbie Bits64 String Prelude.id
test = MkBarbie 10012 "Gundi" 46

testMay : Barbie Bits64 String Maybe
testMay = MkBarbie Nothing Nothing Nothing

--------------------------------------------------------------------------------
--          Recursion
--------------------------------------------------------------------------------

record Recursive where
  constructor MkRecursive
  maybeMe  : Maybe Recursive

%runElab derive "Recursive" [Show, Eq, Ord]

data L1 : Type -> Type where
  MkL1 : (a, Maybe (L1 a)) -> L1 a

%runElab derive "L1" [Show, Eq, Ord]

data Full a = Leaf a | Node (Full (a, a))

%runElab derive "Full" [Show, Eq, Ord]

--------------------------------------------------------------------------------
--          Mutual Recursion
--------------------------------------------------------------------------------

data Tree : Type -> Type where

record Forest a where
  constructor MkForest
  forest : List (Tree a)

data Tree : Type -> Type where
  Empty  : Tree a
  Branch : a -> Forest a -> Tree a

%runElab deriveMutual ["Tree","Forest"] [Show, Eq, Ord]

--------------------------------------------------------------------------------
--          Expr
--------------------------------------------------------------------------------

data Expr : Type -> Type where
  BLit  : Bool -> Expr Bool
  NLit  : Nat  -> Expr Nat
  Succ  : Expr Nat -> Expr Nat
  Plus  : Expr Nat -> Expr Nat -> Expr Nat
  Mult  : Expr Nat -> Expr Nat -> Expr Nat
  NatEq : Expr Nat -> Expr Nat -> Expr Bool
  GTE   : Expr Nat -> Expr Nat -> Expr Bool
  ITE   : Expr Bool -> Expr a -> Expr a -> Expr a

export %hint
eqExprImpl : Eq (Expr t)
eqExprImpl = deriveEq

export %hint
showExprImpl : Show (Expr t)
showExprImpl = deriveShow

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

record Matrix m n a where
  constructor MkMatrix
  runMatrix : Vect m (Vect n a)

%hint
showMatrix : Show a => Show (Matrix m n a)
showMatrix = deriveShow

%hint
eqMatrix : Eq a => Eq (Matrix m n a)
eqMatrix = deriveEq

%hint
ordMatrix : Ord a => Ord (Matrix m n a)
ordMatrix = deriveOrd

public export
data Op : (n : Nat) -> Type where
  Neg : Op 1
  Add : Op 2

%runElab deriveGeneral ["Op"] [Enum]

data TM : Type -> Type where
  Var : a -> TM a
  Call : Op n -> Vect n (TM a) -> TM a
  Lam : TM (Maybe a) -> TM a

%hint
showTm : Show a => Show (TM a)
showTm = deriveShow

data IVect : {n : Nat} -> (a : Type) -> Type where
  MkIVect : (v : Vect n a) -> IVect {n} a

%hint
showIVect : {m : Nat} -> Show a => Show (IVect {n = m} a)
showIVect = deriveShow

--------------------------------------------------------------------------------
--          Semigroup
--------------------------------------------------------------------------------

record Semi where
  constructor MkSemi
  x : List Nat
  y : String
  z : Maybe Bits8

%runElab derive "Semi" [Show,Eq]
%runElab deriveRecord "Semi" [Semigroup,Monoid]

--------------------------------------------------------------------------------
--          elab-util types
--------------------------------------------------------------------------------

%runElab derive "PiInfo" [Show]

%runElab derive "Count" [Show]

%runElab derive "Language.Reflection.Syntax.Arg" [Eq,Show]

%runElab deriveGeneral ["Language.Reflection.Types.MissingInfo"] [Enum]

%hint
showAppArg : Show (AppArg a)
showAppArg = deriveShow

%hint
showAppArgs : Show (Vect.Quantifiers.All.All AppArg vs)
showAppArgs = deriveShow

%hint
showCon : Show (Con n vs)
showCon = deriveShow

%hint
showInfo : Show TypeInfo
showInfo = deriveShow

%hint
eqTpe : Eq (Tpe t)
eqTpe = deriveEq

%hint
showTpe : Show (Tpe t)
showTpe = deriveShow

%hint
eqParam : Eq (Param t)
eqParam = deriveEq

%hint
showParam : Show (Param t)
showParam = deriveShow

Show FC where show _ = "fc"

%hint
showPArg : Show (PArg n)
showPArg = deriveShow

%hint
showConArg : Show (ConArg n)
showConArg = deriveShow

%hint
showParamCon : Show (ParamCon n)
showParamCon = deriveShow

%hint
showParams : Show (Vect.Quantifiers.All.All Param vs)
showParams = deriveShow

%hint
showParamTypeInfo : Show ParamTypeInfo
showParamTypeInfo = deriveShow
