module Test.NameLookup

import Language.Reflection.Syntax.Ops
import Language.Reflection.Util

%language ElabReflection
%default total

Name1 : Name
Name1 = fst $ %runElab lookupName "Either"

0 name1Prf : Name1 === "Prelude.Types.Either"
name1Prf = Refl

record Either where
  constructor MkEither

Name2 : Name
Name2 = fst $ %runElab lookupName "Either"

0 name2Prf : Name2 === "Test.NameLookup.Either"
name2Prf = Refl

namespace Either
  record Either where
    constructor MkEither

  export
  Name3 : Name
  Name3 = fst $ %runElab lookupName "Either"

  0 name3Prf : Name3 === "Test.NameLookup.Either.Either"
  name3Prf = Refl
