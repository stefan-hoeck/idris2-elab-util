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
module Language.Elab.Pretty

import public Data.HVect
import Data.Strings
import public Language.Reflection
import public Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Render.String

--------------------------------------------------------------------------------
--          Utils
--------------------------------------------------------------------------------

||| Pretty but uncolored output to the terminal
export
putPretty : Pretty t => t -> IO ()
putPretty t = putDoc (pretty {ann = ()} t) *> putStrLn ""

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
alignInfix : (fun : String) -> (args : List (Doc ann)) -> Doc ann
alignInfix fun []       = pretty fun
alignInfix fun [type]   = pretty fun <++> type
alignInfix fun (h :: t) =
  let fun' = pretty ("`" ++ fun ++ "`")
      h'   = flatAlt (spaces (cast $ length fun + 3) <+> h) h
   in align $ sep (h' :: map (fun' <++>) t)

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
  prettyPrec p (PI x)  = apply p "PI" [x]
  prettyPrec _ PATTERN = "PATTERN"
  prettyPrec _ NONE    = "NONE"

export
Pretty UseSide where
  pretty UseLeft  = "UseLeft"
  pretty UseRight = "UseRight"

export
Pretty DotReason where
  pretty NonLinearVar   = "NonLinearVar"
  pretty VarApplied     = "VarApplied"
  pretty NotConstructor = "NotConstructor"
  pretty ErasedArg      = "ErasedArg"
  pretty UserDotted     = "UserDotted"
  pretty UnknownDot     = "UnknownDot"

export
Pretty DataOpt where
  prettyPrec p (SearchBy xs) = apply p "SearchBy" xs
  prettyPrec _ NoHints       = "NoHints"
  prettyPrec _ UniqueSearch  = "UniqueSearch"
  prettyPrec _ External      = "External"
  prettyPrec _ NoNewtype     = "NoNewtype"

mutual

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
  Pretty FnOpt where
    prettyPrec _ Inline         = "Inline"
    prettyPrec _ TCInline       = "TCInline"
    prettyPrec p (Hint x)       = apply p "Hint" [x]
    prettyPrec p (GlobalHint x) = apply p "GlobalHint" [x]
    prettyPrec _ ExternFn       = "ExternFn"
    prettyPrec p (ForeignFn xs) = apply p "ForeignFn" xs
    prettyPrec _ Invertible     = "Invertible"
    prettyPrec p (Totalty x)    = apply p "Totality" [x]
    prettyPrec _ Macro          = "Macro"
    prettyPrec p (SpecArgs xs)  = apply p "SpecArgs" xs

  export
  Pretty ITy where
    prettyPrec p (MkTy x n t) = applyH p "MkTy" [n, t]

  export
  Pretty Data where
    prettyPrec p (MkData _ n t o cons) =
      indentLines (applyH p "MkData" [n,t,o]) (map pretty cons)

    prettyPrec p (MkLater _ n tycon) = applyH p "MkLater" [n, tycon]

  export
  Pretty IField where
    prettyPrec p (MkIField _ cnt piInfo name ttImp) =
      applyH p "MkIField" [cnt,piInfo,name,ttImp]

  export
  Pretty Record where
    prettyPrec p (MkRecord _ n ps c fs) = 
      indentLines (applyH p "MkRecord" [n,ps,c]) (map pretty fs)

  export
  Pretty Clause where
    prettyPrec p (PatClause _ l r) = applyH p "PatClause" [l, r]
      
    prettyPrec p (ImpossibleClause _ l) = applyH p "Impossible" [l]

    prettyPrec p (WithClause _ l w cs) =
      indentLines (applyH p "WithClause" [l,w]) (map pretty cs)

  private
  prettyParams : List (Name,TTImp) -> Doc ann
  prettyParams = align . sep . map prettyParam
    where prettyParam : (Name,TTImp) -> Doc ann
          prettyParam (n,ty) = hcat ["(",pretty n," : ", pretty ty,")"]

  export
  Pretty Decl where
    prettyPrec p (IClaim _ c v o t) = applyH p "IClaim" [c,v,o,t]
    prettyPrec p (IData _ v d) = applyH p "IData" [v,d]

    prettyPrec p (IDef _ n cs) =
      indentLines (apply p "IDef" [n]) (map pretty cs)

    prettyPrec p (IParameters _ ps decs) =
      indentLines (apply p "IParameters" [ps]) (map pretty decs)

    prettyPrec p (IRecord _ v r) = applyH p "IRecord" [v, r]

    prettyPrec p (INamespace _ ns ds) =
      indentLines (applyDoc p "INamespace" [dotted ns]) (map pretty ds)

    prettyPrec p (ITransform _ n a b) = applyH p "ITransform" [n,a,b]
    prettyPrec p (ILog k) = apply p "ILog" [k]

  export
  Pretty TTImp where
    prettyPrec p (IVar _ y) = apply p "IVar" [y]

    prettyPrec p x@(IPi _ _ _ _ _ _) =
      backtickParens p (alignInfix "IPi"  $ args x)
      where args : TTImp -> List (Doc ann)
            args (IPi _ c i n at rt) =
              parens (hsepH [c,i,maybe ":" ((++ " :") . show) n,at]) :: args rt

            args rt = [prettyBacktick rt]

    prettyPrec p x@(ILam _ _ _ _ _ _) =
      backtickParens p (alignInfix "ILam" $ args x)
      where args : TTImp -> List (Doc ann)
            args (ILam _ c i n at rt) =
              parens (hsepH [c,i,maybe ":" ((++ " :") . show) n,at]) :: args rt

            args rt = [prettyBacktick rt]

    prettyPrec p (ILet _ cnt name nTy nVal scope) =
      applyH p "ILet" [cnt,name,nTy,nVal,scope]

    prettyPrec p (ICase _ arg ty clauses) = 
      indentLines (applyH p "ICase" [arg,ty]) (map pretty clauses)

    prettyPrec p (ILocal _ decls tt) = 
      indentLines (apply p "ILocal" [tt]) (map pretty decls)

    prettyPrec p (IUpdate _ ups tt) =
      indentLines (apply p"IUpdate" [tt]) (map pretty ups)

    prettyPrec p x@(IApp _ _ _) =
      backtickParens p (alignInfix "IApp" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (IApp _ f t) = prettyBacktick t :: args f
            args t            = [prettyBacktick t]

    prettyPrec p x@(IImplicitApp _ _ _ _) =
      backtickParens p (alignInfix "IImplicitApp" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (IImplicitApp _ f n t) = parens (hsepH[n,":",t]) :: args f
            args t                      = [prettyBacktick t]

    prettyPrec p x@(IWithApp _ _ _) =
      backtickParens p (alignInfix "IWithApp" $ reverse (args x))
      where args : TTImp -> List (Doc ann)
            args (IWithApp _ f t) = prettyBacktick t :: args f
            args t                = [prettyBacktick t]

    prettyPrec p (ISearch _ depth) = applyH p "ISearch" [depth]

    prettyPrec p (IAlternative _ alt xs) =
      indentLines (apply p "IAlternative" [alt]) (map pretty xs)

    prettyPrec p (IRewrite _ y z)   = applyH p "IRewrite" [y, z]
    prettyPrec p (IBindHere _ y z)  = applyH p "IBindHere" [y, z]
    prettyPrec p (IBindVar _ y)     = apply p "IBindVar" [y]
    prettyPrec p (IAs _ use n w)    = applyH p "IAs" [use,n,w]
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
    prettyPrec p (Implicit _ y)     = apply p "IImplicit" [y]
    prettyPrec p (IWithUnambigNames _ xs y) = applyH p "IWithUnabigNames" [xs,y]
