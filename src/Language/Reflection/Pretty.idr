||| Pretty Printing of Elab Data-Types
|||
||| This has not been cleaned-up so, it actually might not
||| look very pretty.
|||
||| This module can be used in the repl to evaluate, how
||| syntax is translated to TTImp and Decl representations.
||| Use `putPretty` together with a quoted expression and
||| inspect the underlying implementation.
|||
||| REPL Examples:
|||
|||   :exec putPretty `{{ Name.In.A.Namespace }}
|||   :exec putPretty `(Just (7 * x))
|||   :exec putPretty `((1 index : Fin n) -> Vect n t -> t)
module Language.Reflection.Pretty

import public Data.HVect
import Data.String
import public Language.Reflection
import public Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.String

%default total

--------------------------------------------------------------------------------
--          Utils
--------------------------------------------------------------------------------

||| Pretty but uncolored output to the terminal
export
putPretty : Pretty t => t -> IO ()
putPretty t = putDoc (indent 2 $ vsep ["", pretty {ann = ()} t, "",""])

||| Constraint, witnessing that all types in the given
||| `Vect` of types have a `Pretty` instance.
public export
AllPretty : Vect n Type -> Type
AllPretty []        = ()
AllPretty (x :: xs) = (Pretty x, AllPretty xs)

||| Convert all values in a heterogeneous vector
||| to `Doc`s using their `Pretty` instances.
export
prettyPrecAll : AllPretty ts => Prec -> HVect ts -> List (Doc ann)
prettyPrecAll _ []       = []
prettyPrecAll p (x :: y) = prettyPrec p x :: prettyPrecAll p y

||| Alias for `prettyPrecAll Open`
export
prettyAll : AllPretty ts => HVect ts -> List (Doc ann)
prettyAll = prettyPrecAll Open

||| Alias for `prettyPrecAll App`
export
prettyAppAll : AllPretty ts => HVect ts -> List (Doc ann)
prettyAppAll = prettyPrecAll App

||| Alias for `hsep . prettyAll`
export
hsepH : AllPretty ts => HVect ts -> Doc ann
hsepH = hsep . prettyAll

||| Alias for `vsep . prettyAll`
export
vsepH : AllPretty ts => HVect ts -> Doc ann
vsepH = vsep . prettyAll

||| Alias for `hcat . prettyAll`
export
hcatH : AllPretty ts => HVect ts -> Doc ann
hcatH = hcat . prettyAll

||| Alias for `vcat . prettyAll`
export
vcatH : AllPretty ts => HVect ts -> Doc ann
vcatH = vcat . prettyAll

||| Alias for `sep . prettyAll`
export
sepH : AllPretty ts => HVect ts -> Doc ann
sepH = sep . prettyAll

||| Prettifies a list of values and concatenates the
||| results using dots as separators.
|||
||| Example: >> `dotted ["a","b","c"]
|||          "a.b.c"
export
dotted : Pretty t => (args : List t) -> Doc ann
dotted = hcat . punctuate "." . map pretty

||| Alias for `prettyPrec App`
export
prettyApp : Pretty t => t -> Doc ann
prettyApp = prettyPrec App

||| Alias for `prettyPrec Backtick`
|||
||| This is used to prettify infixed functions (`IApp`) and
||| set parentheses correctly.
export
prettyBacktick : Pretty t => t -> Doc ann
prettyBacktick = prettyPrec Backtick

||| Wraps a the given `Doc` in parenthesis if the
||| boolean flag is `True`.
export
docParens : Bool -> Doc ann -> Doc ann
docParens False doc = doc
docParens True  doc = parens doc

||| Wraps a the given `Doc` in parenthesis if `p >= App`.
export
appParens : (p : Prec) -> Doc ann -> Doc ann
appParens p = docParens (p >= App)

||| Wraps a the given `Doc` in parenthesis if `p >= Backtick`.
export
backtickParens : (p : Prec) -> Doc ann -> Doc ann
backtickParens p = docParens (p >= Backtick)

||| Data constructor application: Applies the given constructor `con`
||| to a list of arguments. Arguments will be wrapped in parentheses
||| if necessary and aligned properly.
export
applyDoc : (p : Prec) -> (con : Doc ann) -> (args : List (Doc ann)) -> Doc ann
applyDoc p con args = appParens p $ con <++> align (sep args)

export
apply : Pretty t => (p : Prec) -> (con : Doc ann) -> (args : List t) -> Doc ann
apply p con args = applyDoc p con (map prettyApp args)

export
applyH :  AllPretty ts
       => (p    : Prec)
       -> (con  : Doc ann)
       -> (args : HVect ts)
       -> Doc ann
applyH p con args = applyDoc p con (prettyAppAll args)

export
alignInfix :  (fun : String)
           -> (symbol : String)
           -> (args : List (Doc ann))
           -> Doc ann
alignInfix fun _ []       = pretty fun
alignInfix fun _ [type]   = pretty fun <++> type
alignInfix fun symbol (h :: t) =
  let h' = "." <++> flatAlt (spaces (cast (length symbol) - 1) <+> h) h
   in pretty fun <+> align (sep (h' :: map (pretty symbol <++>) t))

export
indentLines : (header : Doc ann) -> (lines : List (Doc ann)) -> Doc ann
indentLines header lines = align $ vsep [header, indent 2 $ vsep lines]

--------------------------------------------------------------------------------
--          Pretty instances for TT Types
--------------------------------------------------------------------------------

export
Pretty Count where
  pretty M0 = "M0"
  pretty M1 = "M1"
  pretty MW = "MW"

export
Pretty t => Pretty (PiInfo t) where
  prettyPrec _ ImplicitArg     = "ImplicitArg"
  prettyPrec _ ExplicitArg     = "ExplicitArg"
  prettyPrec _ AutoImplicit    = "AutoImplicit"
  prettyPrec p (DefImplicit x) = apply p "DefImplicit" [x]

export
Pretty LazyReason where
  pretty LInf     = "Inf"
  pretty LLazy    = "Lazy"
  pretty LUnknown = "Unknown"

export
Pretty TotalReq where
  pretty Total        = "Total"
  pretty CoveringOnly = "Covering"
  pretty PartialOK    = "Partial"

export
Pretty Visibility where
  pretty Private = "Private"
  pretty Export  = "Export"
  pretty Public  = "Public"

export
Pretty Namespace where
  pretty (MkNS xs) = dotted (reverse xs)

export
Pretty Name where
  pretty = pretty . show

export
Pretty Constant where
  pretty (I x)       = pretty x
  pretty (BI x)      = pretty x
  -- TODO : use `pretty` directly, once #1648 is merged
  pretty (I8 x)      = pretty $ show x
  pretty (I16 x)     = pretty $ show x
  pretty (I32 x)     = pretty $ show x
  pretty (I64 x)     = pretty $ show x
  pretty (B8 x)      = pretty x
  pretty (B16 x)     = pretty x
  pretty (B32 x)     = pretty x
  pretty (B64 x)     = pretty x
  pretty (Str x)     = pretty x
  pretty (Ch x)      = pretty x
  pretty (Db x)      = pretty x
  pretty WorldVal    = "%World"
  pretty IntType     = "Int"
  pretty IntegerType = "Integer"
  pretty Int8Type    = "Int8"
  pretty Int16Type   = "Int16"
  pretty Int32Type   = "Int32"
  pretty Int64Type   = "Int64"
  pretty Bits8Type   = "Bits8"
  pretty Bits16Type  = "Bits16"
  pretty Bits32Type  = "Bits32"
  pretty Bits64Type  = "Bits64"
  pretty StringType  = "String"
  pretty CharType    = "Char"
  pretty DoubleType  = "Double"
  pretty WorldType   = "World"


--------------------------------------------------------------------------------
--          Pretty instance for TTImp
--------------------------------------------------------------------------------


export
Pretty BindMode where
  prettyPrec p (PI x)   = apply p "PI" [x]
  prettyPrec _ PATTERN  = "PATTERN"
  prettyPrec _ NONE     = "NONE"
  prettyPrec _ COVERAGE = "COVERAGE"

export
Pretty UseSide where
  pretty UseLeft  = "UseLeft"
  pretty UseRight = "UseRight"

export
Pretty DotReason where
  pretty NonLinearVar    = "NonLinearVar"
  pretty VarApplied      = "VarApplied"
  pretty NotConstructor  = "NotConstructor"
  pretty ErasedArg       = "ErasedArg"
  pretty UserDotted      = "UserDotted"
  pretty UnknownDot      = "UnknownDot"
  pretty UnderAppliedCon = "UnderAppliedCon"

export
Pretty BuiltinType where
  pretty BuiltinNatural = "BuiltinNatural"
  pretty NaturalToInteger = "NaturalToInteger"
  pretty IntegerToNatural = "IntegerToNatural"

export
Pretty WithFlag where
  pretty Syntactic = "Syntactic"

export
Pretty DataOpt where
  prettyPrec p (SearchBy xs) = apply p "SearchBy" xs
  prettyPrec _ NoHints       = "NoHints"
  prettyPrec _ UniqueSearch  = "UniqueSearch"
  prettyPrec _ External      = "External"
  prettyPrec _ NoNewtype     = "NoNewtype"

mutual

  %default covering

  export
  Pretty IFieldUpdate where
    prettyPrec p (ISetField path x) =
      applyDoc p "ISetField" [dotted path, prettyApp x]

    prettyPrec p (ISetFieldApp path x) =
      applyDoc p "ISetFieldApp" [dotted path, prettyApp x]

  export
  Pretty AltType where
    prettyPrec _ FirstSuccess      = "FirstSuccess"
    prettyPrec _ Unique            = "Unique"
    prettyPrec p (UniqueDefault x) = apply p "UniqueDefault" [x]

  export
  Pretty NoMangleDirective where
    prettyPrec p (CommonName x)   = apply p "CommonName" [x]
    prettyPrec p (BackendNames x) = apply p "BackendNames" [x]

  export
  Pretty FnOpt where
    prettyPrec _ Inline         = "Inline"
    prettyPrec _ NoInline       = "NoInline"
    prettyPrec p (NoMangle x)   = apply p "NoMangle" [x]
    prettyPrec _ TCInline       = "TCInline"
    prettyPrec _ Deprecate      = "Deprecate"
    prettyPrec p (Hint x)       = apply p "Hint" [x]
    prettyPrec p (GlobalHint x) = apply p "GlobalHint" [x]
    prettyPrec _ ExternFn       = "ExternFn"
    prettyPrec p (ForeignFn xs) = apply p "ForeignFn" xs
    prettyPrec _ Invertible     = "Invertible"
    prettyPrec p (Totality x)   = apply p "Totality" [x]
    prettyPrec _ Macro          = "Macro"
    prettyPrec p (SpecArgs xs)  = apply p "SpecArgs" xs

  export
  Pretty ITy where
    prettyPrec p (MkTy _ _ n t) = applyH p "MkTy" [n, t]

  export
  Pretty Data where
    prettyPrec p (MkData _ n t o cs) = applyH p "MkData" [n,t,o,cs]
    prettyPrec p (MkLater _ n tycon) = applyH p "MkLater" [n, tycon]

  export
  Pretty IField where
    prettyPrec p (MkIField _ c pi n t) = applyH p "MkIField" [c,pi,n,t]

  export
  Pretty Record where
    prettyPrec p (MkRecord _ n ps c fs) = applyH p "MkRecord" [n,ps,c,fs]

  export
  Pretty Clause where
    prettyPrec p (PatClause _ l r) = applyH p "PatClause" [l, r]
    prettyPrec p (ImpossibleClause _ l) = applyH p "Impossible" [l]
    prettyPrec p (WithClause _ l w prf fs cs) = applyH p "WithClause" [l,w,prf,fs,cs]

  export
  Pretty Decl where
    prettyPrec p (IBuiltin _ b n) = applyH p "IBuiltin" [b,n]
    prettyPrec p (IRunElabDecl _ t) = applyH p "IRunElabDecl" [t]
    prettyPrec p (IClaim _ c v o t) = applyH p "IClaim" [c,v,o,t]
    prettyPrec p (IData _ v d) = applyH p "IData" [v,d]
    prettyPrec p (IDef _ n cs) = applyH p "IDef" [n,cs]
    prettyPrec p (IParameters _ ps decs) = applyH p "IParameters" [ps,decs]
    prettyPrec p (IRecord _ n v r) = applyH p "IRecord" [n, v, r]
    prettyPrec p (INamespace _ (MkNS ns) ds) =
      indentLines (applyDoc p "INamespace" [dotted ns]) (map pretty ds)

    prettyPrec p (ITransform _ n a b) = applyH p "ITransform" [n,a,b]
    prettyPrec p (ILog k) = apply p "ILog" [k]

  export
  Pretty TTImp where
    prettyPrec p (IVar _ y) = apply p "IVar" [y]

    prettyPrec p x@(IPi _ _ _ _ _ _) =
      backtickParens p (alignInfix "IPi" "->" $ args x)
      where args : TTImp -> List (Doc ann)
            args (IPi _ c i n at rt) =
              parens (hsepH [c,i,maybe ":" ((++ " :") . show) n,at]) :: args rt

            args rt = [prettyBacktick rt]

    prettyPrec p x@(ILam _ _ _ _ _ _) =
      backtickParens p (alignInfix "ILam" "=>" $ args x)
      where args : TTImp -> List (Doc ann)
            args (ILam _ c i n at rt) =
              parens (hsepH [c,i,maybe ":" ((++ " :") . show) n,at]) :: args rt

            args rt = [prettyBacktick rt]

    prettyPrec p (ILet _ _ cnt name nTy nVal scope) =
      applyH p "ILet" [cnt,name,nTy,nVal,scope]

    prettyPrec p (ICase _ arg ty cs) = applyH p "ICase" [arg,ty,cs]

    prettyPrec p (ILocal _ decls tt) =
      indentLines (apply p "ILocal" [tt]) (map pretty decls)

    prettyPrec p (IUpdate _ ups tt) = applyH p"IUpdate" [ups,tt]

    prettyPrec p x@(IApp _ _ _) =
      backtickParens p (alignInfix "IApp" "$" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (IApp _ f t) = prettyBacktick t :: args f
            args t            = [prettyBacktick t]

    prettyPrec p x@(IAutoApp _ _ _) =
      backtickParens p (alignInfix "IAutoApp" "$" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (IAutoApp _ f t) = prettyBacktick t :: args f
            args t                = [prettyBacktick t]

    prettyPrec p x@(INamedApp _ _ _ _) =
      backtickParens p (alignInfix "INamedApp" "$" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (INamedApp _ f n t) = prettyBacktick t :: args f
            args t                   = [prettyBacktick t]

--    prettyPrec p x@(IImplicitApp _ _ _ _) =
--      backtickParens p (alignInfix "IImplicitApp" "$" $ reverse (args x))
--      where args : TTImp -> List (Doc ann)
--            args (IImplicitApp _ f n t) = parens (hsepH[n,":",t]) :: args f
--            args t                      = [prettyBacktick t]

    prettyPrec p x@(IWithApp _ _ _) =
      backtickParens p (alignInfix "IWithApp" "$" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (IWithApp _ f t) = prettyBacktick t :: args f
            args t                = [prettyBacktick t]

    prettyPrec p (ISearch _ depth) = applyH p "ISearch" [depth]

    prettyPrec p (IAlternative _ alt xs) = applyH p "IAlternative" [alt,xs]

    prettyPrec p (IRewrite _ y z)   = applyH p "IRewrite" [y, z]
    prettyPrec p (IBindHere _ y z)  = applyH p "IBindHere" [y, z]
    prettyPrec p (IBindVar _ y)     = apply p "IBindVar" [y]
    prettyPrec p (IAs _ _ use n w)  = applyH p "IAs" [use,n,w]
    prettyPrec p (IMustUnify _ y z) = applyH p "IMustUnify" [y,z]
    prettyPrec p (IDelayed _ y z)   = applyH p "IDelayed" [y,z]
    prettyPrec p (IDelay _ y)       = apply p "IDelay" [y]
    prettyPrec p (IForce _ y)       = apply p "IForce" [y]
    prettyPrec p (IQuote _ y)       = apply p "IQuote" [y]
    prettyPrec p (IQuoteName _ y)   = apply p "IQuoteName" [y]
    prettyPrec p (IQuoteDecl _ y)   = apply p "IQuoteDecl" [y]
    prettyPrec p (IUnquote _ y)     = apply p "IUnquote" [y]
    prettyPrec p (IPrimVal _ y)     = apply p "IPrimVal" [y]
    prettyPrec _ (IType _)          = "IType"
    prettyPrec p (IHole _ y)        = apply p "IHole" [y]
    prettyPrec p (Implicit _ y)     = apply p "Implicit" [y]
    prettyPrec p (IWithUnambigNames _ xs y) = applyH p "IWithUnabigNames" [xs,y]
