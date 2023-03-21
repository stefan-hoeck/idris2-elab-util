module Test.Derive

import Language.Reflection.Pretty
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

%runElab derive "Elem" [Show,Eq,Ord]

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
-- --------------------------------------------------------------------------------

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

info : TypeInfo
info = getInfo "Barbie"

-- %logging "derive.claims" 1
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
--          Indexed Types
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

%runElab deriveIndexed "Expr" [Show, Eq, Ord]

record Matrix m n a where
  constructor MkMatrix
  runMatrix : Vect m (Vect n a)

%runElab derivePattern "Matrix" [I,I,P] [Show, Eq, Ord]

public export
data Op : (n : Nat) -> Type where
  Neg : Op 1
  Add : Op 2

%runElab deriveIndexed "Op" [Show,Eq,Ord]

data TM : Type -> Type where
  Var : a -> TM a
  Call : Op n -> Vect n (TM a) -> TM a
  Lam : TM (Maybe a) -> TM a

%runElab derive "TM" [Show]

data IVect : {n : Nat} -> (a : Type) -> Type where
  MkIVect : (v : Vect n a) -> IVect {n} a

%runElab derivePattern "IVect" [I,P] [Show]

--------------------------------------------------------------------------------
--          Semigroup
--------------------------------------------------------------------------------

record Semi where
  constructor MkSemi
  x : List Nat
  y : String
  z : Maybe Bits8

%runElab derive "Semi" [Show,Eq,Semigroup,Monoid]

--------------------------------------------------------------------------------
--          Num
--------------------------------------------------------------------------------

record V3 a where
  constructor MkV3
  x : a
  y : a
  z : a

%runElab derive "V3"
  [Show,Eq,Semigroup,Monoid,Num,Neg,Abs,Integral,FromDouble,Fractional]

--------------------------------------------------------------------------------
--          fromInteger
--------------------------------------------------------------------------------

record V4 a where
  constructor MkV4
  w : a
  x : a
  y : a
  z : a

%runElab derive "V4" [Show,Eq,FromInteger]

--------------------------------------------------------------------------------
--          elab-util types
--------------------------------------------------------------------------------

%runElab derive "PiInfo" [Show]

%runElab derive "Count" [Show]

%runElab derive "Language.Reflection.Syntax.Arg" [Eq,Show]

%runElab deriveIndexed "Language.Reflection.Types.MissingInfo" [Show,Eq,Ord]

%runElab deriveIndexed "Language.Reflection.Types.AppArg" [Show]

--------------------------------------------------------------------------------
--          Tagged
--------------------------------------------------------------------------------

record Id (v : k) where
  constructor MkId
  value : Nat

namespace Id
  %runElab derive "Id" [Show,Eq,Ord,FromInteger]
