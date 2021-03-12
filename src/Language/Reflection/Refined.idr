||| The content of this module is based on the
||| tutorial post about [refined primitives](../../Doc/Primitives.md).
module Language.Reflection.Refined

import public Data.Maybe
import public Data.So
import public Language.Reflection.Derive

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

--------------------------------------------------------------------------------
--          Elab Scripts
--------------------------------------------------------------------------------

||| Creates an `Eq` implementation for the given datatype
||| by using the given accessor function.
|||
||| This is hardly useful on its own but convenient when
||| combined with other interface implementors.
|||
||| ```idris example
||| record AtomicNr where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedEq "AtomicNr" `{{value}}
||| ```
export covering
refinedEq : (dataType : String) -> (accessor : Name) -> Elab ()
refinedEq dt accessor =
  let eqFun   = UN $ "implEq"   ++ dt
      tpe     = varStr dt
      acc     = var accessor

   in declare
        [ interfaceHint Public eqFun `(Eq ~(tpe))
        , def eqFun [patClause (var eqFun) `(mkEq ((==) `on` ~(acc)))]
        ]

||| Creates an `Ord` implementation for the given datatype
||| by using the given accessor function.
|||
||| This is hardly useful on its own but convenient when
||| combined with other interface implementors.
|||
||| ```idris example
||| record AtomicNr where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedOrd "AtomicNr" `{{value}}
||| ```
export covering
refinedOrd : (dataType : String) -> (accessor : Name) -> Elab ()
refinedOrd dt accessor =
  let ordFun  = UN $ "implOrd"  ++ dt

      tpe     = varStr dt
      acc     = var accessor

   in declare
        [ interfaceHint Public ordFun `(Ord ~(tpe))
        , def ordFun [patClause (var ordFun) `(mkOrd (compare `on` ~(acc)))]
        ]

||| Creates a `Show` implementation for the given datatype
||| by using the given accessor function.
|||
||| This is hardly useful on its own but convenient when
||| combined with other interface implementors.
|||
||| ```idris example
||| record AtomicNr where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedShow "AtomicNr" `{{value}}
||| ```
export covering
refinedShow : (dataType : String) -> (accessor : Name) -> Elab ()
refinedShow dt accessor =
  let showFun = UN $ "implShow" ++ dt

      tpe     = varStr dt
      acc     = var accessor

   in declare
        [ interfaceHint Public showFun `(Show ~(tpe))
        , def showFun [patClause (var showFun)
                       `(mkShowPrec (\p => showPrec p . ~(acc)))]
        ]

||| Convenience function combining `refinedEq`, `refinedOrd`,
||| and `refinedShow`.
export covering
refinedEqOrdShow : (dataType : String) -> (accessor : Name) -> Elab ()
refinedEqOrdShow dt acc = do refinedEq dt acc
                             refinedOrd dt acc
                             refinedShow dt acc

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined integral number.
|||
||| Conversion functions are called `refine` and `fromInteger`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record AtomicNr where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedIntegral "AtomicNr"
|||                          `{{MkAtomicNr}}
|||                          `{{value}}
|||                          `(Int)
||| ```
|||
||| The above will result in the following declarations being generated:
|||
||| ```idris example
||| Eq AtomicNr where
|||   (==) = (==) `on` value
|||
||| Ord AtomicNr where
|||   compare = compare `on` value
|||
||| Show AtomicNr where
|||   showPrec p = showPrec p . value
|||
||| namespace AtomicNr
|||   refine : Int -> Maybe AtomicNr
|||   refine = refineSo MkAtomicNr
|||
|||   fromInteger :  (v : Integer)
|||               -> {auto 0 _: IsJust (refine $ fromInteger v)}
|||               -> AtomicNr
|||   fromInteger v = fromJust (refine $ fromInteger v)
||| ```
export covering
refinedIntegral :  (dataType : String)
                -> (con      : Name)
                -> (accessor : Name)
                -> (tpe      : TTImp)
                -> Elab ()
refinedIntegral dt con acc tpe =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : ~(tpe) -> Maybe ~(varStr dt)
             refine = refineSo ~(var con)

             public export
             fromInteger :  (n : Integer)
                         -> {auto 0 _: IsJust (~(refineNS) $ fromInteger n)}
                         -> ~(varStr dt)
             fromInteger n = fromJust (refine $ fromInteger n)
           ]
        ]

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
|||
||| ```idris example
||| record AtomicNr where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedInt "AtomicNr"
||| ```
export covering
refinedInt : (dataType : String) -> Elab ()
refinedInt dt = refinedIntegral dt (UN $ "Mk" ++ dt) `{{value}} `(Int)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export covering
refinedBits8 : (dataType : String) -> Elab ()
refinedBits8 dt = refinedIntegral dt (UN $ "Mk" ++ dt) `{{value}} `(Bits8)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export covering
refinedBits16 : (dataType : String) -> Elab ()
refinedBits16 dt = refinedIntegral dt (UN $ "Mk" ++ dt) `{{value}} `(Bits16)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export covering
refinedBits32 : (dataType : String) -> Elab ()
refinedBits32 dt = refinedIntegral dt (UN $ "Mk" ++ dt) `{{value}} `(Bits32)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export covering
refinedBits64 : (dataType : String) -> Elab ()
refinedBits64 dt = refinedIntegral dt (UN $ "Mk" ++ dt) `{{value}} `(Bits64)

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined floating point
||| number.
|||
||| Conversion functions are called `refine` and `fromDouble`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record Abundance where
|||   constructor MkAbundance
|||   value : Double
|||   0 inBounds : So (0 < value && value <= 1)
|||
||| %runElab refinedFloating "Abundance" `{{MkAbundance}} `{{value}}
||| ```
|||
||| The above will result in the following declarations being generated:
|||
||| ```idris example
||| Eq Abundance where
|||   (==) = (==) `on` value
|||
||| Ord Abundance where
|||   compare = compare `on` value
|||
||| Show Abundance where
|||   showPrec p = showPrec p . value
|||
||| namespace Abundance
|||   refine : Double -> Maybe Abundance
|||   refine = refineSo MkAbundance
|||
|||   fromDouble :  (v : Double)
|||              -> {auto 0 _: IsJust (refine v)}
|||              -> Abundance
|||   fromDouble v = fromJust (refine v)
||| ```
export covering
refinedFloating :  (dataType : String)
                -> (con      : Name)
                -> (accessor : Name)
                -> Elab ()
refinedFloating dt con acc =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : Double -> Maybe ~(varStr dt)
             refine = refineSo ~(var con)

             public export
             fromDouble :  (n : Double)
                        -> {auto 0 _: IsJust (~(refineNS) n)}
                        -> ~(varStr dt)
             fromDouble n = fromJust (refine n)
           ]
        ]

||| Convenience version of `refinedFloating` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export covering
refinedDouble : (dataType : String) -> Elab ()
refinedDouble dt = refinedFloating dt (UN $ "Mk" ++ dt) `{{value}}

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined string value.
|||
||| Conversion functions are called `refine` and `fromString`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record Html where
|||   constructor MkHtml
|||   value : String
|||   0 inBounds : So (isValidHtml value)
|||
||| %runElab refinedText "Html" `{{MkHtml}} `{{value}}
||| ```
|||
||| The above will result in the following declarations being generated:
|||
||| ```idris example
||| Eq Html where
|||   (==) = (==) `on` value
|||
||| Ord Html where
|||   compare = compare `on` value
|||
||| Show Html where
|||   showPrec p = showPrec p . value
|||
||| namespace Html
|||   refine : String -> Maybe Html
|||   refine = refineSo MkHtml
|||
|||   fromString :  (v : String)
|||              -> {auto 0 _: IsJust (refine v)}
|||              -> Html
|||   fromString v = fromJust (refine v)
||| ```
export covering
refinedText :  (dataType : String)
            -> (con      : Name)
            -> (accessor : Name)
            -> Elab ()
refinedText dt con acc =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : String -> Maybe ~(varStr dt)
             refine = refineSo ~(var con)

             public export
             fromString :  (n : String)
                        -> {auto 0 _: IsJust (~(refineNS) n)}
                        -> ~(varStr dt)
             fromString n = fromJust (refine n)
           ]
        ]

||| Convenience version of `refinedText` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export covering
refinedString : (dataType : String) -> Elab ()
refinedString dt = refinedText dt (UN $ "Mk" ++ dt) `{{value}}
