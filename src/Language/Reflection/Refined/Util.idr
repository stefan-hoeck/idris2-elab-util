||| Utilities for Language.Reflection.Refined
module Language.Reflection.Refined.Util

import public Data.Maybe
import public Data.So

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
maybeSo : (b : Bool) -> Maybe (So b)
maybeSo True  = Just Oh
maybeSo False = Nothing

public export
refineSo :  {f : a -> Bool}
         -> (make : (v : a) -> (0 prf : So $ f v) -> b)
         -> (val : a)
         -> Maybe b
refineSo make val = case maybeSo (f val) of
                         Just oh => Just $ make val oh
                         Nothing => Nothing
