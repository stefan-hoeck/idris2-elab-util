||| Pretty Printing of Elab Data-Types
|||
||| This has not been cleaned-up so, it actually might not
||| look very pretty.
module Language.Elab.Pretty

import public Data.HVect
import Data.Strings
import Language.Reflection
import Text.PrettyPrint.Prettyprinter

--------------------------------------------------------------------------------
--          Utils
--------------------------------------------------------------------------------

public export
AllPretty : Vect n Type -> Type
AllPretty []        = ()
AllPretty (x :: xs) = (Pretty x, AllPretty xs)

export
prettyAll : AllPretty ts => HVect ts -> List (Doc ann)
prettyAll []       = []
prettyAll (x :: y) = pretty x :: prettyAll y

export
hsepH : AllPretty ts => HVect ts -> Doc ann
hsepH = hsep . prettyAll

export
vsepH : AllPretty ts => HVect ts -> Doc ann
vsepH = vsep . prettyAll

export
sepH : AllPretty ts => HVect ts -> Doc ann
sepH = sep . prettyAll

export
docParens : Bool -> Doc ann -> Doc ann
docParens False doc = doc
docParens True  doc = parens doc

export
applyArg : Pretty t => t -> Doc ann
applyArg = prettyPrec App

export
applyPrefixDoc :  (p : Prec)
               -> (prefix_ : Doc ann)
               -> (args : List (Doc ann))
               -> Doc ann
applyPrefixDoc p prefix_ args = docParens (p >= App) 
                              $ align (sep $ prefix_ :: args)

export
applyPrefix :  Pretty t
            => (p : Prec)
            -> (prefix_ : Doc ann)
            -> (args : List t)
            -> Doc ann
applyPrefix p prefix_ args = applyPrefixDoc p prefix_ (map applyArg args)

export
dotted : Pretty t => (args : List t) -> Doc ann
dotted = hcat . punctuate "." . map pretty

export
fun : (args : List (Doc ann)) -> (type : Doc ann) -> Doc ann
fun [] type       = ":" <++> type
fun (h :: t) type = align 
                  $ sep 
                  $ [": " <++> h] ++ map ("->" <++>) t ++ ["->" <++> type]

export
prettyFun :  (Pretty arg, Pretty tpe)
          => (args : List arg)
          -> (type : tpe)
          -> Doc ann
prettyFun args type = fun (map pretty args) (pretty type)
  
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
  prettyPrec p (DefImplicit x) = applyPrefix p "DefImplicit" [x]

export
Pretty LazyReason where
  pretty LInf     = "LInf"
  pretty LLazy    = "LLazy"
  pretty LUnknown = "LUnknown"

export
Pretty TotalReq where
  pretty Total        = "Total"
  pretty CoveringOnly = "CoveringOnly"
  pretty PartialOK    = "PartialOK"

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
  prettyPrec p (UN n)    = pretty n
  prettyPrec p (MN n i)  = hcat ["{",pretty n,":",pretty i,"}"]
  prettyPrec p (NS ns n) = pretty n
  prettyPrec p (DN s _)  = pretty s
  prettyPrec p (RF s)    = pretty s

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
  prettyPrec p (PI x)  = applyPrefix p "PI" [x]
  prettyPrec p PATTERN = "PATTERN"
  prettyPrec p NONE    = "NONE"

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
  prettyPrec p (SearchBy xs) = applyPrefix p "SearchBy" xs
  prettyPrec p NoHints       = "NoHints"
  prettyPrec p UniqueSearch  = "UniqueSearch"
  prettyPrec p External      = "External"
  prettyPrec p NoNewtype     = "NoNewtype"

mutual

  export
  Pretty IFieldUpdate where
    prettyPrec p (ISetField path x) =
      applyPrefixDoc p "ISetField" [dotted path, applyArg x]

    prettyPrec p (ISetFieldApp path x) =
      applyPrefixDoc p "ISetFieldApp" [dotted path, applyArg x]

  export
  Pretty AltType where
    prettyPrec p FirstSuccess      = "FirstSuccess"
    prettyPrec p Unique            = "Unique"
    prettyPrec p (UniqueDefault x) = applyPrefix p "UniqueDefault" [x]

  export
  Pretty FnOpt where
    prettyPrec p Inline         = "Inline"
    prettyPrec p TCInline       = "TCInline"
    prettyPrec p (Hint x)       = applyPrefix p "Hint" [x]
    prettyPrec p (GlobalHint x) = applyPrefix p "GlobalHint" [x]
    prettyPrec p ExternFn       = "ExternFn"
    prettyPrec p (ForeignFn xs) = applyPrefix p "ForeignFn" xs
    prettyPrec p Invertible     = "Invertible"
    prettyPrec p (Totalty x)    = applyPrefix p "Totality" [x]
    prettyPrec p Macro          = "Macro"
    prettyPrec p (SpecArgs xs)  = applyPrefix p "SpecArgs" xs

  export
  Pretty ITy where
    prettyPrec p (MkTy x n t) = applyPrefixDoc p "Ty" [applyArg n, applyArg t]

  export
  Pretty Data where
    prettyPrec p (MkData _ n tycon opts datacons) =
      let docs = applyArg tycon :: (map applyArg opts ++ map applyArg datacons)
       in applyPrefixDoc p ("Data" <++> pretty n) docs

    prettyPrec p (MkLater _ n tycon) =
       applyPrefix p ("Data" <++> pretty n) [tycon]

  export
  Pretty IField where
    prettyPrec p (MkIField _ cnt piInfo name ttImp) =
      let pre = hsep ["Field", applyArg cnt, applyArg piInfo, applyArg name]
       in applyPrefix p pre [ttImp]

  export
  Pretty Record where
    prettyPrec p (MkRecord _ name params conName fields) = 
      let header = applyPrefix p (pretty "Record" <++> pretty name) [params]
          con    = pretty "constructor" <++> pretty conName
          lines  = indent 2 $ vsep (con :: map pretty fields)
       in vsep [header,lines]

  export
  Pretty Clause where
    pretty (PatClause _ lh rh) = align $ sep [pretty lh <++> "=", pretty rh]
      
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

    pretty (IDef _ name clauses) = vsep (pretty name :: map pretty clauses)

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

    prettyPrec p pi@(IPi _ _ _ _ _ _) = "pi" <++> uncurry fun (args pi)
       where args : TTImp -> (List (Doc ann), Doc ann)
             args (IPi _ c i n argTy retTy) =
               let (as,ty) = args retTy
                   a       = parens $ hsepH [c,i,maybe "" show n,":",argTy]
                in (a::as,ty)

             args retTy = ([], pretty retTy)

    prettyPrec p la@(ILam _ _ _ _ _ _) = "lambda" <++> uncurry fun (args la)
       where args : TTImp -> (List (Doc ann), Doc ann)
             args (ILam _ c i n argTy retTy) =
               let (as,ty) = args retTy
                   a       = parens $ hsepH [c,i,maybe "" show n,":",argTy]
                in (a::as,ty)

             args retTy = ([], pretty retTy)

    prettyPrec p (ILet _ cnt name nTy nVal scope) =
      hsepH ["let", cnt, name, ":", nTy, "=", nVal]


    prettyPrec p (ICase _ arg ty clauses) = 
      vsep [ "case" <++> parens (pretty arg <++> ":" <++> pretty ty)
           , indent 2 $ vsep (map pretty clauses) ]

    prettyPrec p (ILocal _ decls tt) = 
      vsep ["local", indent 2 $ vsep (map pretty decls ++ [pretty tt])]

    prettyPrec p (IUpdate _ ups tt) =
      vsep ["update", indent 2 $ vsep (map pretty ups ++ [pretty tt])]

    prettyPrec p (IApp _ f tt) = 
      align $ sep [pretty f <++> "`app`", pretty tt]

    prettyPrec p (IImplicitApp _ f name tt) =
      let dispName = maybe neutral pretty name
       in align $ sep [pretty f <++> "`impApp`" <++> dispName, pretty tt]

    prettyPrec p (IWithApp _ f tt) =
      align $ sep ["withApp" <++> pretty f, pretty tt]

    prettyPrec p (ISearch _ depth) = "search" <++> pretty depth

    prettyPrec p (IAlternative _ alt xs) =
      vsep ["alternative" <++> pretty alt, indent 2 $ vsep (map pretty xs)]

    prettyPrec p (IRewrite _ y z) =
      align $ sepH ["rewrite", y, z]

    prettyPrec p (IBindHere _ y z) = hsepH ["bind here", y, z]

    prettyPrec p (IBindVar _ y) = "bindVar" <++> pretty y

    prettyPrec p (IAs _ use name w) =
      hsep ["as", pretty use, pretty name <+> "@" <+> prettyPrec App w]

    prettyPrec p (IMustUnify _ y z) = hsepH ["mustUnify", y, z]

    prettyPrec p (IDelayed _ y z) = hsepH ["delayed", y, z]

    prettyPrec p (IDelay _ y) = hsepH ["delay", y]
    prettyPrec p (IForce _ y) = hsepH ["force", y]
    prettyPrec p (IQuote _ y) = hsepH ["quote", y]
    prettyPrec p (IQuoteName _ y) = hsepH ["quoteName", y]
    prettyPrec p (IQuoteDecl _ y) = hsepH ["quoteDecl", y]
    prettyPrec p (IUnquote _ y) = hsepH ["unquote", y]
    prettyPrec p (IPrimVal _ c) = pretty c
    prettyPrec p (IType _) = "Type"
    prettyPrec p (IHole _ y) = "?" <+> pretty y
    prettyPrec p (Implicit _ bindIfUnsolved) = "implicit" <++> pretty bindIfUnsolved
    prettyPrec p (IWithUnambigNames _ xs y) = "with names" <++> pretty xs <++> pretty y
