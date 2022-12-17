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

import Derive.Pretty
import Data.String
import Language.Reflection.Syntax
import Language.Reflection.Types

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Utils
--------------------------------------------------------------------------------

public export
Opts80 : LayoutOpts
Opts80 = Opts 80

||| Pretty but uncolored output to the terminal
export %inline
putDoc : HasIO io => Doc Opts80 -> io ()
putDoc = putStr . render Opts80

||| Pretty but uncolored output to the terminal
export %inline
putPretty : HasIO io => Pretty t => t -> io ()
putPretty = putDoc . pretty

public export
0 WithName : Type -> Type
WithName = Pair String

export
conH :
     {opts : _}
  -> All Pretty ts
  => Prec
  -> String
  -> All Prelude.id ts
  -> Doc opts
conH p str ps = prettyCon p str $ go ps
  where go : All Pretty ss => All Prelude.id ss -> List (Doc opts)
        go @{[]}     []             = []
        go @{_ :: _} (v :: ps) = prettyArg v :: go ps

export
recordH :
     {opts : _}
  -> All Pretty ts
  => Prec
  -> String
  -> All WithName ts
  -> Doc opts
recordH p str ps = prettyRecord p str $ go ps
  where go : All Pretty ss => All WithName ss -> List (Doc opts)
        go @{[]}     []             = []
        go @{_ :: _} ((fn,v) :: ps) = prettyField fn v :: go ps

--------------------------------------------------------------------------------
--          Pretty instances for TT Types
--------------------------------------------------------------------------------

public export
Pretty Namespace where
  prettyPrec _ (MkNS xs) = line . concat . intersperse "." $ reverse xs

export
Pretty Name where
  prettyPrec _ = line . show

export
Pretty FC where
  prettyPrec _ _ = line "fc"


%runElab derive "Count" [Pretty]
%runElab derive "PiInfo" [Pretty]
%runElab derive "LazyReason" [Pretty]
%runElab derive "TotalReq" [Pretty]
%runElab derive "Visibility" [Pretty]
%runElab derive "PrimType" [Pretty]
%runElab derive "Constant" [Pretty]

--------------------------------------------------------------------------------
--          Pretty instance for TTImp
--------------------------------------------------------------------------------

%runElab derive "BindMode" [Pretty]
%runElab derive "UseSide" [Pretty]
%runElab derive "DotReason" [Pretty]
%runElab derive "BuiltinType" [Pretty]
%runElab derive "WithFlag" [Pretty]
%runElab derive "DataOpt" [Pretty]

export %hint
prettyImplTTImp : Pretty TTImp

%runElab deriveMutual
  [ "IFieldUpdate"
  , "AltType"
  , "ITy"
  , "FnOpt"
  , "Data"
  , "IField"
  , "Record"
  , "Clause"
  , "Decl"
  , "Language.Reflection.Syntax.Arg"
  ] [Pretty]

prettyImplTTImp = assert_total $ MkPretty $ \p,v => case v of
  IVar _ nm => conH p "var" [nm]

  IPi _ rig pinfo mnm argTy retTy =>
    recordH p "pi" [("arg", MkArg rig pinfo mnm argTy), ("retTy", retTy)]

  ILam _ rig pinfo mnm argTy lamTy =>
    recordH p "lam" [("arg", MkArg rig pinfo mnm argTy), ("lamTy", lamTy)]

  ILet _ _ rig nm nTy nVal scope =>
    recordH p "ilet"
      [ ("count", rig)
      , ("name", nm)
      , ("type", nTy)
      , ("val", nVal)
      , ("scope", scope)
      ]

  ICase _ s ty cls =>
    recordH p "iCase" [("sc", s), ("ty", ty), ("clauses", cls)]

  ILocal _ decls s => recordH p "local" [("decls", decls), ("scope", s)]

  IUpdate _ upds s => recordH p "update" [("updates", upds), ("arg", s)]

  IApp _ s t => recordH p "app" [("fun", s), ("arg", t)]

  INamedApp _ s nm t =>
    recordH p "namedApp" [("fun", s), ("name", nm), ("arg", t)]

  IAutoApp _ s t => recordH p "autoApp" [("fun", s), ("arg", t)]
  IWithApp _ s t => recordH p "withApp" [("fun", s), ("arg", t)]
  ISearch _ depth => conH p "iSearch" [depth]
  IAlternative _ x ss => recordH p "alternative" [("tpe", x), ("alts", ss)]
  IRewrite _ s t => recordH p "iRewrite" [("eq", s), ("scope", t)]
  IBindHere _ bm s => recordH p "bindHere" [("mode", bm), ("arg", s)]
  IBindVar _ str => conH p "bindVar" [str]
  IAs _ _ side nm s =>
    recordH p "iAs" [("side", side), ("name", nm), ("val", s)]
  IMustUnify _ dr s => recordH p "mustUnify" [("reason", dr), ("val", s)]
  IDelayed _ lr s => recordH p "iDelayed" [("reason", lr), ("arg", s)]
  IDelay _ s => conH p "iDelay" [s]
  IForce _ s => conH p "iForce" [s]
  IQuote _ s => conH p "quote" [s]
  IQuoteName _ nm => conH p "quoteName" [nm]
  IQuoteDecl _ decls => conH p "quoteName" [decls]
  IUnquote _ s => conH p "unquote" [s]
  IPrimVal _ c => conH p "primVal" [c]
  IType _ => line "type"
  IHole _ str => conH p "hole" [str]
  Implicit _ b => conH p "Implicit" [b]
  IWithUnambigNames fc xs s => conH p "IWithUnambigNames" [fc, xs, s]

--------------------------------------------------------------------------------
--          Pretty instances for library types
--------------------------------------------------------------------------------

export
Pretty a => Pretty (Vect n a) where
  prettyPrec p vs = prettyPrec p (toList vs)

export %inline
Pretty (Fin n) where
  prettyPrec _ = line . show

%runElab deriveIndexed "MissingInfo" [Pretty]
%runElab deriveIndexed "AppArg" [Pretty]

export
Pretty (All AppArg vs) where
  prettyPrec _ vs = list $ go vs
    where go : All AppArg bs -> List (Doc opts)
          go []       = []
          go (x :: y) = pretty x :: go y

%runElab deriveIndexed "Con" [Pretty]
%runElab deriveIndexed "TypeInfo" [Pretty]
%runElab deriveIndexed "ParamTag" [Pretty]

export
Pretty (ParamPattern m n) where
  prettyPrec _ vs = list $ go vs
    where go : ParamPattern x y -> List (Doc opts)
          go []       = []
          go (x :: y) = pretty x :: go y

%runElab deriveIndexed "PArg" [Pretty]
%runElab deriveIndexed "ConArg" [Pretty]
%runElab deriveIndexed "ParamCon" [Pretty]
%runElab deriveIndexed "ParamTypeInfo" [Pretty]
