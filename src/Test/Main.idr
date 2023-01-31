module Test.Main

import Derive.Pretty
import Language.Reflection.Pretty
import Test.Derive
import Test.Enum1
import Test.Enum2
import Test.Generic2
import Test.Inspect
import Test.NameLookup
import Test.TypeInfo

main : IO ()
main = putStrLn "All tests passed"
