||| The content of this module is based on the
||| tutorial post about [refined primitives](../../Doc/Primitives.md).
module Language.Reflection.Refined

import public Language.Reflection.Refined.Util
import public Language.Reflection.Derive

%default total

--------------------------------------------------------------------------------
--          Elab Scripts
--------------------------------------------------------------------------------

||| Creates an `Eq` implementation for the given datatype
||| by using the given accessor function.
|||
||| This is hardly useful on its own but convenient when
||| combined with other interface implementors.
|||
||| In some occasions it is useful to have one or several
||| phantom types for the refined type. Therefore, the exact
||| type should be given as a `TTImp`.
|||
||| ```idris example
||| record AtomicNr a where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedEq "AtomicNr" `(AtomicNr a) `{{value}}
||| ```
export
refinedEq : (dataType : String) -> (dt : TTImp) -> (accessor : Name) -> Elab ()
refinedEq dt t accessor =
  let eqFun   = UN $ "implEq"   ++ dt
      acc     = var accessor

   in declare
        [ interfaceHint Public eqFun `(Eq ~(t))
        , def eqFun [patClause (var eqFun) `(mkEq ((==) `on` ~(acc)))]
        ]

||| Creates an `Ord` implementation for the given datatype
||| by using the given accessor function.
|||
||| This is hardly useful on its own but convenient when
||| combined with other interface implementors.
|||
||| ```idris example
||| record AtomicNr a where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedOrd "AtomicNr" `(AtomicNr a) `{{value}}
||| ```
export
refinedOrd : (dataType : String) -> (dt : TTImp) -> (accessor : Name) -> Elab ()
refinedOrd dt t accessor =
  let ordFun  = UN $ "implOrd"  ++ dt
      acc     = var accessor

   in declare
        [ interfaceHint Public ordFun `(Ord ~(t))
        , def ordFun [patClause (var ordFun) `(mkOrd (compare `on` ~(acc)))]
        ]

||| Creates a `Show` implementation for the given datatype
||| by using the given accessor function.
|||
||| This is hardly useful on its own but convenient when
||| combined with other interface implementors.
|||
||| ```idris example
||| record AtomicNr a where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedShow "AtomicNr" `(AtomicNr a) `{{value}}
||| ```
export
refinedShow : (dataType : String) -> (dt : TTImp) -> (accessor : Name) -> Elab ()
refinedShow dt t accessor =
  let showFun = UN $ "implShow" ++ dt
      acc     = var accessor

   in declare
        [ interfaceHint Public showFun `(Show ~(t))
        , def showFun [patClause (var showFun)
                       `(mkShowPrec (\p => showPrec p . ~(acc)))]
        ]

||| Convenience function combining `refinedEq`, `refinedOrd`,
||| and `refinedShow`.
export
refinedEqOrdShow :  (dataType : String)
                 -> (dt : TTImp)
                 -> (accessor : Name)
                 -> Elab ()
refinedEqOrdShow dt t acc = do refinedEq dt t acc
                               refinedOrd dt t acc
                               refinedShow dt t acc

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined integral number.
|||
||| Conversion functions are called `refine` and `fromInteger`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record AtomicNr a where
|||   constructor MkAtomicNr
|||   value : Int
|||   0 inBounds : So (1 <= value && value <= 118)
|||
||| %runElab refinedIntegral "AtomicNr"
|||                          `(AtomicNr a)
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
export
refinedIntegral :  (dataType : String)
                -> (dt       : TTImp)
                -> (con      : Name)
                -> (accessor : Name)
                -> (tpe      : TTImp)
                -> Elab ()
refinedIntegral dt t con acc tpe =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in refinedEqOrdShow dt t acc >>
      declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : ~(tpe) -> Maybe ~(t)
             refine = refineSo ~(var con)

             public export
             fromInteger :  (n : Integer)
                         -> {auto 0 _: IsJust (~(refineNS) $ fromInteger n)}
                         -> ~(t)
             fromInteger n = fromJust (refine $ fromInteger n)
           ]
        ]

export
refinedIntegralDflt : (dataType : String) -> (tpe : TTImp) -> Elab ()
refinedIntegralDflt dt tpe =
  refinedIntegral dt (varStr dt) (UN $ "Mk" ++ dt) `{value} tpe

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
export
refinedInt : (dataType : String) -> Elab ()
refinedInt dt = refinedIntegralDflt dt `(Int)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedBits8 : (dataType : String) -> Elab ()
refinedBits8 dt = refinedIntegralDflt dt `(Bits8)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedBits16 : (dataType : String) -> Elab ()
refinedBits16 dt = refinedIntegralDflt dt `(Bits16)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedBits32 : (dataType : String) -> Elab ()
refinedBits32 dt = refinedIntegralDflt dt `(Bits32)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedBits64 : (dataType : String) -> Elab ()
refinedBits64 dt = refinedIntegralDflt dt `(Bits64)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedInt8 : (dataType : String) -> Elab ()
refinedInt8 dt = refinedIntegralDflt dt `(Int8)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedInt16 : (dataType : String) -> Elab ()
refinedInt16 dt = refinedIntegralDflt dt `(Int16)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedInt32 : (dataType : String) -> Elab ()
refinedInt32 dt = refinedIntegralDflt dt `(Int32)

||| Specialized version of `refinedIntegral` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedInt64 : (dataType : String) -> Elab ()
refinedInt64 dt = refinedIntegralDflt dt `(Int64)

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined floating point
||| number.
|||
||| Conversion functions are called `refine` and `fromDouble`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record Abundance a where
|||   constructor MkAbundance
|||   value : Double
|||   0 inBounds : So (0 < value && value <= 1)
|||
||| %runElab refinedFloating "Abundance" `(Abundance a) `{{MkAbundance}} `{{value}}
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
export
refinedFloating :  (dataType : String)
                -> (dt       : TTImp)
                -> (con      : Name)
                -> (accessor : Name)
                -> Elab ()
refinedFloating dt t con acc =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in refinedEqOrdShow dt t acc >>
      declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : Double -> Maybe ~(t)
             refine = refineSo ~(var con)

             public export
             fromDouble :  (n : Double)
                        -> {auto 0 _: IsJust (~(refineNS) n)}
                        -> ~(t)
             fromDouble n = fromJust (refine n)
           ]
        ]

||| Convenience version of `refinedFloating` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedDouble : (dataType : String) -> Elab ()
refinedDouble dt = refinedFloating dt (varStr dt) (UN $ "Mk" ++ dt) `{value}

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined string value.
|||
||| Conversion functions are called `refine` and `fromString`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record Html a where
|||   constructor MkHtml
|||   value : String
|||   0 inBounds : So (isValidHtml value)
|||
||| %runElab refinedText "Html" `(Html a) `{{MkHtml}} `{{value}}
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
export
refinedText :  (dataType : String)
            -> (dt       : TTImp)
            -> (con      : Name)
            -> (accessor : Name)
            -> Elab ()
refinedText dt t con acc =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in refinedEqOrdShow dt t acc >>
      declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : String -> Maybe ~(t)
             refine = refineSo ~(var con)

             public export
             fromString :  (n : String)
                        -> {auto 0 _: IsJust (~(refineNS) n)}
                        -> ~(t)
             fromString n = fromJust (refine n)
           ]
        ]

||| Convenience version of `refinedText` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Int is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedString : (dataType : String) -> Elab ()
refinedString dt = refinedText dt (varStr dt) (UN $ "Mk" ++ dt) `{value}

||| This creates `Eq`, `Ord`, and `Show` implementations as
||| well as conversion functions for a refined charater.
|||
||| Conversion functions are called `refine` and `fromChar`
||| and are put in their own namespace, named after the
||| data type's name.
|||
||| ```idris example
||| record Digit a where
|||   constructor MkDigit
|||   value : Char
|||   0 inBounds : So (isDigit value)
|||
||| %runElab refinedText "Digit" `(Digit a) `{{MkDigit}} `{{value}}
||| ```
|||
||| The above will result in the following declarations being generated:
|||
||| ```idris example
||| Eq Digit where
|||   (==) = (==) `on` value
|||
||| Ord Digit where
|||   compare = compare `on` value
|||
||| Show Digit where
|||   showPrec p = showPrec p . value
|||
||| namespace Digit
|||   refine : Char -> Maybe Digit
|||   refine = refineSo MkDigit
|||
|||   fromChar :  (v : Char)
|||            -> {auto 0 _: IsJust (refine v)}
|||            -> Digit
|||   fromChar v = fromJust (refine v)
||| ```
export
refinedCharacter :  (dataType : String)
                 -> (dt       : TTImp)
                 -> (con      : Name)
                 -> (accessor : Name)
                 -> Elab ()
refinedCharacter dt t con acc =
  let ns   = MkNS [dt]

      -- this has to be namespaced
      -- to avoid disambiguities when being used
      -- in fromInteger
      refineNS = var $ NS ns (UN "refine")

   in refinedEqOrdShow dt t acc >>
      declare
        [ INamespace EmptyFC ns
          `[ public export
             refine : Char -> Maybe ~(t)
             refine = refineSo ~(var con)

             public export
             fromChar :  (n : Char)
                      -> {auto 0 _: IsJust (~(refineNS) n)}
                      -> ~(t)
             fromChar n = fromJust (refine n)
           ]
        ]

||| Convenience version of `refinedCharacter` for data types,
||| which adhere to the following conventions:
|||
|||  * If a data type's name is `Foo` its constructor is named `MkFoo`.
|||  * The field accessor of the wrapped Char is named `value`.
|||  * The proof of validity consists of a single zero quantity `So`.
export
refinedChar : (dataType : String) -> Elab ()
refinedChar dt = refinedCharacter dt (varStr dt) (UN $ "Mk" ++ dt) `{value}
