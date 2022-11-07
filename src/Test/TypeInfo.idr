module Test.TypeInfo

import Data.List
import Language.Reflection.Types

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Enum Types
--------------------------------------------------------------------------------

BoolInfo : TypeInfo
BoolInfo = getInfo "Bool"

0 boolInfoArity : arty BoolInfo === 0
boolInfoArity = Refl

0 boolIsEnum : isEnum BoolInfo === True
boolIsEnum = Refl

--------------------------------------------------------------------------------
--          Parameters
--------------------------------------------------------------------------------

implArgName : NamedArg -> Maybe Name
implArgName (MkArg M0 ImplicitArg name _) = Just name
implArgName _                             = Nothing

implConArgNames : Con n -> List Name
implConArgNames (MkCon _ args _) = mapMaybe implArgName args

implArgNames : TypeInfo -> List Name
implArgNames (MkTypeInfo _ _ _ cs) =
  toList cs >>= implConArgNames

data Foo : (a : Type) -> (b : Type) -> Type where
  MkFoo : Either y x -> Foo a b

FooInfo : TypeInfo
FooInfo = getInfo "Foo"

0 fooInfoArity : arty FooInfo === 2
fooInfoArity = Refl

0 fooNotEnum : isEnum FooInfo === False
fooNotEnum = Refl

-- as can be seen here, erased implicits are added in reverse order
-- of appearance
0 fooArgNames : implArgNames FooInfo === ["b", "a", "x", "y"]
fooArgNames = Refl
