||| Pretty Printing of Elab Data-Types
|||
||| This module can be used in the repl to evaluate, how
||| syntax is translated to TTImp and Decl representations.
||| Use `putPretty` together with a quoted expression and
||| inspect the underlying implementation.
|||
||| Note, to improve readability, some constructs are pretty printed
||| as infix operator chains. The operators in question can be found in
||| module `Language.Reflection.Syntax.Ops`.
|||
||| REPL Examples:
|||
|||   :exec putPretty `{{ Name.In.A.Namespace }}
|||   :exec putPretty `(Just (7 * x))
|||   :exec putPretty `((1 index : Fin n) -> Vect n t -> t)
module Language.Reflection.Pretty

import Derive.Pretty
import Data.String
import Data.Vect.Quantifiers
import Language.Reflection.Util
import Language.Reflection.TTImp

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
  -> {auto _ : All Pretty ts}
  -> Prec
  -> String
  -> All Prelude.id ts
  -> Doc opts
conH p str ps = prettyCon p str $ go ps

  where
    go : All Pretty ss => All Prelude.id ss -> List (Doc opts)
    go @{[]}     []             = []
    go @{_ :: _} (v :: ps) = prettyArg v :: go ps

export
recordH :
     {opts : _}
  -> {auto _ : All Pretty ts}
  -> Prec
  -> String
  -> All WithName ts
  -> Doc opts
recordH p str ps = prettyRecord p str $ go ps

  where
    go : All Pretty ss => All WithName ss -> List (Doc opts)
    go @{[]}     []             = []
    go @{_ :: _} ((fn,v) :: ps) = prettyField fn v :: go ps

export
op :
     {opts : _}
  -> Prec
  -> (fixity : Nat)
  -> (fst  : Doc opts)
  -> (args : List (String,Doc opts))
  -> Doc opts
op p fixity fst args@((o,_) :: _) =
  let len    := length o
      opArgs := map (\(x,y) => line {opts} x <++> y) args
      sngl   := hsep (fst :: opArgs)
      mult   := vsep (indent (S len) fst :: opArgs)
   in parenthesise (p >= User fixity) $ ifMultiline sngl mult
op _ _ fst [] = fst

--------------------------------------------------------------------------------
--          Pretty instances for TT Types
--------------------------------------------------------------------------------

public export
Pretty Namespace where
  prettyPrec _ (MkNS xs) = line . concat . intersperse "." $ reverse xs

export
Pretty Name where
  prettyPrec _ = dquotes . line . show

export
Pretty FC where
  prettyPrec _ _ = line "emptyFC"

export
Pretty a => Pretty (WithDefault a def') where
  prettyPrec p withDef =
    onWithDefault (line "defaulted")
                  (\v => prettyCon p "specified" [prettyArg v])
                  withDef

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

export %hint
prettyImplArg : Pretty Arg

export %hint
prettyImplClause : Pretty Clause

export %hint
prettyImplITy : Pretty ITy

%runElab deriveMutual
  [ "IFieldUpdate"
  , "AltType"
  , "FnOpt"
  , "Data"
  , "IField"
  , "Record"
  , "Decl"
  ] [Pretty]

prettyImplITy = MkPretty $ \p,v => case v of
  (MkTy _ _ n ty) => recordH p "mkTy" [("name", n), ("type", ty)]

prettyImplArg = MkPretty $ \p,v =>
  conH p "MkArg" [v.count, v.piInfo, v.name, v.type]

prettyImplClause = assert_total $ MkPretty $ \p,v => case v of
  PatClause fc lhs rhs =>
    op p 3 (prettyPrec (User 3) lhs) [(".=", prettyPrec (User 3) rhs)]
  WithClause fc lhs rig wval prf flags cls =>
    recordH p "withClause"
      [ ("lhs", lhs)
      , ("rig", rig)
      , ("wval", wval)
      , ("prf", prf)
      , ("flags", flags)
      , ("clauses", cls)
      ]
  ImpossibleClause fc lhs => conH p "impossibleClause" [lhs]

appOp : {opts : _} -> Either String Name -> TTImp -> (String, Doc opts)
appOp (Left x)  s = (x, prettyPrec (User 6) s)
appOp (Right x) s = (".!", prettyPrec (User 6) (x,s))

appPairs :
     {opts : _}
  -> List (String,Doc opts)
  -> TTImp
  -> (Doc opts, List (String,Doc opts))
appPairs ps (IApp fc s t)     = appPairs (appOp (Left ".$") t :: ps) s
appPairs ps (IAutoApp fc s t) = appPairs (appOp (Left ".@") t :: ps) s
appPairs ps (INamedApp fc s nm t) = appPairs (appOp (Right nm) t :: ps) s
appPairs ps t = (prettyPrec (User 6) t, ps)

prettyImplTTImp = assert_total $ MkPretty $ \p,v => case v of
  IVar _ nm => conH p "var" [nm]

  IPi _ rig pinfo mnm argTy retTy =>
    let (args,res) := unPi retTy
        pargs      := prettyPrec (User 5) <$> args
        pres       := prettyPrec (User 5) res
        fst        := prettyPrec (User 5) $ MkArg rig pinfo mnm argTy
     in op p 5 fst $ (".->",) <$> (pargs ++ [pres])

  ILam _ rig pinfo mnm argTy lamTy =>
    let (args,res) := unLambda lamTy
        pargs      := prettyPrec (User 3) <$> args
        pres       := prettyPrec (User 3) res
        fst        := prettyPrec (User 3) $ MkArg rig pinfo mnm argTy
     in op p 3 fst $ (".=>",) <$> (pargs ++ [pres])

  ILet _ _ rig nm nTy nVal scope =>
    recordH p "ilet"
      [ ("count", rig)
      , ("name", nm)
      , ("type", nTy)
      , ("val", nVal)
      , ("scope", scope)
      ]

  ICase _ _ s ty cls =>
    recordH p "iCase" [("sc", s), ("ty", ty), ("clauses", cls)]

  ILocal _ decls s => recordH p "local" [("decls", decls), ("scope", s)]

  IUpdate _ upds s => recordH p "update" [("updates", upds), ("arg", s)]

  IApp _ s t =>
    let (fst,ps) := appPairs [appOp (Left ".$") t] s
     in op p 6 fst ps

  INamedApp _ s nm t =>
    let (fst,ps) := appPairs [appOp (Right nm) t] s
     in op p 6 fst ps

  IAutoApp _ s t =>
    let (fst,ps) := appPairs [appOp (Left ".@") t] s
     in op p 6 fst ps

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
  Implicit _ False => line "implicitFalse"
  Implicit _ True  => line "implicitTrue"
  IWithUnambigNames fc xs s => conH p "IWithUnambigNames" [fc, xs, s]

--------------------------------------------------------------------------------
--          Pretty instances for library types
--------------------------------------------------------------------------------

export %inline
Pretty (Fin n) where
  prettyPrec _ = line . show

%runElab deriveIndexed "MissingInfo" [Pretty]
%runElab deriveIndexed "AppArg" [Pretty]

export
Pretty (All AppArg vs) where
  prettyPrec _ vs = list $ go vs

    where
      go : All AppArg bs -> List (Doc opts)
      go []       = []
      go (x :: y) = pretty x :: go y

%runElab deriveIndexed "Con" [Pretty]
%runElab deriveIndexed "TypeInfo" [Pretty]
%runElab deriveIndexed "ParamTag" [Pretty]

export
Pretty (ParamPattern m n) where
  prettyPrec _ vs = list $ go vs

    where
      go : ParamPattern x y -> List (Doc opts)
      go []       = []
      go (x :: y) = pretty x :: go y

%runElab deriveIndexed "PArg" [Pretty]
%runElab deriveIndexed "ConArg" [Pretty]
%runElab deriveIndexed "ParamCon" [Pretty]
%runElab deriveIndexed "ParamTypeInfo" [Pretty]
