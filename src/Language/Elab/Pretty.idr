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
||| to `Doc`s using the corresponding `Pretty`
||| instances.
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

||| Data constructor application: Applies the given constructor `con`
||| to a list of arguments. Arguments will be wrapped in parentheses
||| if necessary and aligned properly.
export
applyDoc :  (p    : Prec)
         -> (con  : Doc ann)
         -> (args : List (Doc ann))
         -> Doc ann
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
funType : (arrow : Doc ann)
    -> (args : List (Doc ann))
    -> (type : Doc ann)
    -> Doc ann
funType arrow [] type       = ":" <++> type
funType arrow (h :: t) type = align 
                            $ sep 
                            $     [": " <++> h]
                               ++ map (arrow <++>) t
                               ++ [arrow <++> type]

export
pi : (args : List (Doc ann)) -> (type : Doc ann) -> Doc ann
pi = funType "->"

export
lambda : (args : List (Doc ann)) -> (type : Doc ann) -> Doc ann
lambda = funType "=>"

export
prettyPi :  (Pretty arg, Pretty tpe)
         => (args : List arg)
         -> (type : tpe)
         -> Doc ann
prettyPi args type = pi (map pretty args) (pretty type)
  
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
  prettyPrec p (DefImplicit x) = applyH p "DefImplicit" [x]

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
    prettyPrec p (MkData _ n tycon opts datacons) =
      vsep [ applyH p "MkData" [n,tycon,opts]
           , indent 2 $ vsep (map pretty datacons)
           ]

    prettyPrec p (MkLater _ n tycon) = applyH p "MkLater" [n, tycon]

  export
  Pretty IField where
    prettyPrec p (MkIField _ cnt piInfo name ttImp) =
      applyH p "MkIField" [cnt,piInfo,name,ttImp]

  export
  Pretty Record where
    prettyPrec p (MkRecord _ name params conName fields) = 
      vsep [ applyH p "MkRecord" [name,params,conName]
           , indent 2 $ vsep (map pretty fields)
           ]

  export
  Pretty Clause where
    pretty (PatClause _ lh rh) = 
      "PatClause" <++> align ( sep [ "  " <++> pretty lh
                                   , "=>" <++> pretty rh])
      
    pretty (ImpossibleClause _ lh) = pretty lh <++> "impossible"

    pretty (WithClause _ lh wval xs) =
      let lines = indent 2 $ vsep (map pretty xs)
       in vsep [pretty lh <++> pretty wval, lines]

  private
  prettyParams : List (Name,TTImp) -> Doc ann
  prettyParams = align . sep . map prettyParam
    where prettyParam : (Name,TTImp) -> Doc ann
          prettyParam (n,ty) = hcat ["(",pretty n," : ", pretty ty,")"]

  export
  Pretty Decl where
    pretty (IClaim _ cnt vis opts ty) =
      let prettyOpts = hcat $ punctuate ";" (map pretty opts)
       in vsep [pretty cnt, pretty vis, prettyOpts, pretty ty]

    pretty (IData _ vis dat) = vsepH [vis, dat]

    pretty (IDef _ name clauses) = vsep $ map (\c => hsepH [name,":",c]) clauses

    pretty (IParameters _ ps decs) = vsep (prettyParams ps :: map pretty decs)

    pretty (IRecord _ v r) = vsepH [v, r]

    pretty (INamespace _ names decls) =
      let head = pretty "namespace" <++> dotted names
       in vsep (head :: map pretty decls)

    pretty (ITransform _ name a b) = vsepH [name, a, b]

    pretty (ILog k) = "log" <++> pretty k

  export
  Pretty TTImp where
    prettyPrec p (IVar _ y) = "IVar" <++> prettyPrec p y

    prettyPrec _ p@(IPi _ _ _ _ _ _) = "pi" <++> uncurry pi (args p)
       where args : TTImp -> (List (Doc ann), Doc ann)
             args (IPi _ c i n argTy retTy) =
               let (as,ty) = args retTy
                   a       = parens $ hsepH [c,i,maybe "" show n,":",argTy]
                in (a::as,ty)

             args retTy = ([], pretty retTy)

    prettyPrec p la@(ILam _ _ _ _ _ _) =
       docParens (p >= App) ("lambda" <++> uncurry lambda (args la))
       where args : TTImp -> (List (Doc ann), Doc ann)
             args (ILam _ c i n argTy retTy) =
               let (as,ty) = args retTy
                   a       = parens $ hsepH [c,i,maybe "" show n,":",argTy]
                in (a::as,ty)

             args retTy = ([], pretty retTy)

    prettyPrec p (ILet _ cnt name nTy nVal scope) =
      "let" <++> parens (hsepH [cnt, name, ":", nTy]) <++> "=" <++> pretty nVal


    prettyPrec p (ICase _ arg ty clauses) = 
      vsep [ "case" <++> parens (pretty arg <++> ":" <++> pretty ty) <++> "of"
           , indent 2 $ vsep (map pretty clauses) ]

    prettyPrec p (ILocal _ decls tt) = 
      vsep ["local", indent 2 $ vsep (map pretty decls ++ [pretty tt])]

    prettyPrec p (IUpdate _ ups tt) =
      vsep ["update", indent 2 $ vsep (map pretty ups ++ [pretty tt])]

    prettyPrec p (IApp _ f tt) =
       docParens (p >= App)
       (align $ sep [prettyPrec p f <++> "`app`", prettyApp tt])

    prettyPrec p (IImplicitApp _ f name tt) =
      let dispName = maybe neutral pretty name
       in align $ sep [pretty f <++> "`impApp`" <++> dispName, pretty tt]

    prettyPrec p (IWithApp _ f tt) =
      align $ sep ["withApp" <++> pretty f, pretty tt]

    prettyPrec p (ISearch _ depth) = "search" <++> pretty depth

    prettyPrec p (IAlternative _ alt xs) =
      vsep ["alternative" <++> pretty alt, indent 2 $ vsep (map pretty xs)]

    prettyPrec p (IRewrite _ y z) = align $ sepH ["rewrite", y, z]

    prettyPrec p (IBindHere _ y z) = hsepH ["bind here", y, z]

    prettyPrec p (IBindVar _ y) = "bindVar" <++> pretty y

    prettyPrec p (IAs _ use name w) =
      hsep ["as", pretty use, pretty name <+> "@" <+> prettyApp w]

    prettyPrec p (IMustUnify _ y z) = hsepH ["mustUnify", y, z]
    prettyPrec p (IDelayed _ y z)   = hsepH ["delayed", y, z]
    prettyPrec p (IDelay _ y)       = hsepH ["delay", y]
    prettyPrec p (IForce _ y)       = hsepH ["force", y]
    prettyPrec p (IQuote _ y)       = "`("  <++> pretty y <++> ")"
    prettyPrec p (IQuoteName _ y)   = "`{{" <++> pretty y <++> "}}"
    prettyPrec p (IQuoteDecl _ y)   = "`["  <++> pretty y <++> "]"
    prettyPrec p (IUnquote _ y)     = "~("  <++> pretty y <++> ")"
    prettyPrec p (IPrimVal _ c)     = pretty c
    prettyPrec p (IType _)          = "Type"
    prettyPrec p (IHole _ y)        = "?" <+> prettyPrec p y
    prettyPrec p (Implicit _ bind)  =   "{Implicit:" <+> pretty bind <+> "}"
    prettyPrec p (IWithUnambigNames _ xs y) = "with names" <++> pretty xs <++> pretty y
