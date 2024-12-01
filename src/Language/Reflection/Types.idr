module Language.Reflection.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import Data.Vect
import Data.Vect.Quantifiers
import Language.Reflection
import Language.Reflection.Syntax

%language ElabReflection

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
Res : Type -> Type
Res = Either String

||| Creates a sequence of argument names, using the given string as a prefix
||| and appending names with their index in the sequence.
|||
||| It is at times necessary to provide a set of fresh names to
||| for instance pattern matching on a data constructor making sure
||| to not shadow already existing
||| names. This function provides a pure way to do so without having
||| to run this in the `Elab` monad.
export
freshNames : String -> (n : Nat) -> Vect n String
freshNames s = go 0

  where
    go : Nat -> (k : Nat) -> Vect k String
    go m 0     = []
    go m (S k) = (s ++ show m) :: go (S m) k

public export
implicits : Foldable t => t Name -> List Arg
implicits = map erasedImplicit . toList

||| Tries to generate the given proofs for all values in the
||| given vector over an applicative functor.
public export
tryAll :
     {0 a : Type}
  -> {0 p : a -> Type}
  -> {auto _ : Applicative f}
  -> ((v : a) -> f (p v))
  -> (vs : Vect n a)
  -> f (All p vs)
tryAll g []        = pure []
tryAll g (x :: xs) = [| g x :: tryAll g xs |]

--------------------------------------------------------------------------------
--          Applied Arguments
--------------------------------------------------------------------------------

public export
data MissingInfo : PiInfo TTImp -> Type where
  Auto     : MissingInfo AutoImplicit
  Implicit : MissingInfo ImplicitArg
  Deflt    : MissingInfo (DefImplicit t)

export
Uninhabited (MissingInfo ExplicitArg) where
  uninhabited Auto impossible
  uninhabited Implicit impossible
  uninhabited Deflt impossible

||| An argument extracted from an applied function.
|||
||| We use these to match result types of data constructors against the
||| arguments of the corresponding type constructor, so they
||| are indexed by the corresponding argument.
public export
data AppArg : Arg -> Type where
  ||| Named application: `foo {x = 12}`
  NamedApp : (n : Name) -> TTImp -> AppArg (MkArg c p (Just n) t)

  ||| Applying an unnamed auto implicit: `foo @{MyEq}`
  AutoApp  : TTImp -> AppArg (MkArg c AutoImplicit n t)

  ||| Regular function application: `foo 12`.
  Regular  : TTImp -> AppArg (MkArg c ExplicitArg n t)

  ||| An implicit argument not given explicitly.
  Missing  : MissingInfo p -> AppArg (MkArg c p n t)

public export
(.ttimp) : AppArg a -> TTImp
(.ttimp) (NamedApp nm s) = s
(.ttimp) (Regular s)     = s
(.ttimp) (AutoApp s)     = s
(.ttimp) (Missing x)     = implicitFalse

||| Applies an argument to the given value.
public export
appArg : TTImp -> AppArg a -> TTImp
appArg t (NamedApp nm s) = namedApp t nm s
appArg t (AutoApp s)     = autoApp t s
appArg t (Regular s)     = app t s
appArg t (Missing _)     = t

||| Sequence of applied arguments matching a list of function arguments.
public export
0 AppArgs : Vect n Arg -> Type
AppArgs = All AppArg

unappVia : (TTImp -> Maybe (a, TTImp)) -> TTImp -> Maybe (a,TTImp)
unappVia f s = case f s of
  Just p  => Just p
  Nothing => case s of
    IApp fc t u         => map (\t' => IApp fc t' u) <$> unappVia f t
    INamedApp fc t nm u => map (\t' => INamedApp fc t' nm u) <$> unappVia f t
    IAutoApp fc t u     => map (\t' => IAutoApp fc t' u) <$> unappVia f t
    _                   => Nothing

-- tries to extract a named argument from an expression
named : (n : Name) -> TTImp -> Maybe (AppArg (MkArg c p (Just n) t), TTImp)
named n =
  unappVia $ \case
    INamedApp fc t nm u =>
      if n == nm then Just (NamedApp n u, t) else Nothing
    _                   => Nothing

-- tries to extract an auto-implicit argument from an expression
getAuto : TTImp -> Maybe (AppArg (MkArg c AutoImplicit n t), TTImp)
getAuto = unappVia $ \case
  IAutoApp fc t u => Just (AutoApp u, t)
  _               => Nothing

-- tries to extract a regular argument from an expression
regular : TTImp -> Maybe (AppArg (MkArg c ExplicitArg n t), TTImp)
regular = unappVia $ \case
  IApp fc t u => Just (Regular u, t)
  _           => Nothing

unnamed : (p : PiInfo TTImp) -> TTImp -> Maybe (AppArg (MkArg c p n t), TTImp)
unnamed ExplicitArg     s = regular s
unnamed ImplicitArg     s = Just (Missing Implicit, s)
unnamed (DefImplicit x) s = Just (Missing Deflt, s)
unnamed AutoImplicit    s = getAuto s <|> Just (Missing Auto, s)

||| Tries to extract an applied argument from an expression,
||| returning it together with the remainder of the expression.
export
getArg : (arg : Arg) -> TTImp -> Maybe (AppArg arg , TTImp)
getArg (MkArg _ pi Nothing _)  s = unnamed pi s
getArg (MkArg _ pi (Just n) _) s = named n s <|> unnamed pi s

argErr : Arg -> String
argErr (MkArg _ _ (Just n) _) = "Missing explicit argument: \{n}"
argErr (MkArg _ _ Nothing t) =
  "Missing unnamed, explicit argument of type: \{show t}"

||| Tries to unapply an expression and extract all
||| applied function arguments.
public export
getArgs : (vs : Vect n Arg) -> TTImp -> Res (AppArgs vs, TTImp)
getArgs (x :: xs) s =
  let Right (vs,s2) := getArgs xs s | Left err => Left err
      Just (v,s3)   := getArg x s2  | Nothing => Left $ argErr x
   in Right (v :: vs, s3)
getArgs []        s = Right ([], s)

--------------------------------------------------------------------------------
--          Constructors
--------------------------------------------------------------------------------

||| Data constructor of a data type index over the list of arguments
||| of the corresponding type constructor.
public export
record  Con (n : Nat) (vs : Vect n Arg) where
  constructor MkCon
  name     : Name
  arty     : Nat
  args     : Vect arty Arg
  typeArgs : AppArgs vs

public export %inline
Named (Con n vs) where
  c.getName = c.name

||| True if the given constructor has only erased arguments.
public export
isConstant : Con n vs -> Bool
isConstant c = all isErased c.args

||| Creates bindings for the explicit arguments of a data constructor
||| using the given prefix plus an index for the name of each
||| argument.
|||
||| This is useful for implementing functions which pattern match on a
||| data constructor.
export
bindCon : (c : Con n vs) -> Vect c.arty String -> TTImp
bindCon c ns = go c.nameVar (map piInfo c.args) ns

  where
    go : TTImp -> Vect k (PiInfo TTImp) -> Vect k String -> TTImp
    go t []                  []        = t
    go t (ExplicitArg :: xs) (n :: ns) = go (t `app` bindVar n) xs ns
    go t (_           :: xs) (n :: ns) = go t xs ns

||| Applies a constructor to variables of the given name.
export
applyCon : (c : Con n vs) -> Vect c.arty Name -> TTImp
applyCon c ns = go c.nameVar (map piInfo c.args) ns

  where
    go : TTImp -> Vect k (PiInfo TTImp) -> Vect k Name -> TTImp
    go t []                  []        = t
    go t (ExplicitArg :: xs) (n :: ns) = go (t `app` var n) xs ns
    go t (_           :: xs) (n :: ns) = go t xs ns

||| Tries to lookup a data constructor by name, based on the
||| given list of arguments of the corresponding data constructor.
export
getCon : Elaboration m => (vs : Vect n Arg) -> Name -> m (Con n vs)
getCon vs n = do
  (n',tt)       <- lookupName n
  let (args,tpe)      := unPi tt
      (arty ** vargs) := (length args ** Vect.fromList args)
  case getArgs vs tpe of
    Right (vs, IVar _ _) => pure $ (MkCon n' arty vargs vs)
    Right (vs, _)        => fail "Unexpected type for constructor \{n}"
    Left err             => fail "Unexpected type for constructor \{n}: \{err}"

||| Information about a data type
|||
||| @name : Name of the data type
|||         Note: There is no guarantee that the name will be fully
|||         qualified
||| @args : Type arguments of the data type
||| @cons : List of data constructors
public export
record TypeInfo where
  constructor MkTypeInfo
  name     : Name
  arty     : Nat
  args     : Vect arty Arg
  argNames : Vect arty Name
  cons     : List (Con arty args)

public export %inline
Named TypeInfo where
  t.getName = t.name

public export
namedArg : (a : Arg) -> Maybe Name
namedArg (MkArg _ _ (Just n) _) = Just n
namedArg _                      = Nothing

||| Returns the names of explicit arguments of a type constructor.
public export
(.explicitArgs) : TypeInfo -> List Name
(.explicitArgs) p = go Lin p.args p.argNames

  where
    go : SnocList Name -> Vect k Arg -> Vect k Name -> List Name
    go sn []        []                              = sn <>> []
    go sn (MkArg _ ExplicitArg _ _ :: xs) (n :: ns) = go (sn :< n) xs ns
    go sn (_                       :: xs) (n :: ns) = go sn xs ns

||| Returns a type constructor
||| applied to the names of its explicit arguments
public export
(.applied) : TypeInfo -> TTImp
(.applied) p = go p.nameVar p.args p.argNames

  where
    go : TTImp -> Vect n Arg -> Vect n Name -> TTImp
    go t []        []          = t
    go t (MkArg _ AutoImplicit _ _ :: xs) (_ :: nms) = go t xs nms
    go t (MkArg _ _ (Just no) _ :: xs) (nm :: nms) =
      go (namedApp t no (var nm)) xs nms
    go t (MkArg _ _ Nothing   _ :: xs) (nm :: nms) =
      go (t `app` var nm) xs nms

||| Returns a list of implicit arguments corresponding
||| to the data type's implicit and explicit arguments.
public export %inline
(.implicits) : TypeInfo -> List Arg
(.implicits) p = go Lin p.args

  where
    toArg : Maybe Name -> TTImp -> Arg
    toArg mn (IHole _ _) = MkArg M0 ImplicitArg mn implicitFalse
    toArg mn t           = MkArg M0 ImplicitArg mn t

    go : SnocList Arg -> Vect k Arg -> List Arg
    go sn []                               = sn <>> []
    go sn (MkArg _ ExplicitArg mn t :: xs) = go (sn :< toArg mn t) xs
    go sn (MkArg _ ImplicitArg mn t :: xs) = go (sn :< toArg mn t) xs
    go sn (_                        :: xs) = go sn xs


||| True if the given type has only constant constructors and
||| is therefore represented by a single unsigned integer at runtime.
public export
isEnum : TypeInfo -> Bool
isEnum ti = all isConstant $ ti.cons

||| True if the given constructor has name `Nil` and no explicit arguments.
public export
isNil : Con n vs -> Bool
isNil (MkCon n _ as _) = isNil n && all (not . isExplicit) as

||| True if the given constructor has name `(::)` and
||| exactly two explicit arguments.
public export
isCons : Con n vs -> Bool
isCons (MkCon n _ as _) = isCons n && count isExplicit as == 2

||| True if the given constructor has name `Lin` and no explicit arguments.
public export
isLin : Con n vs -> Bool
isLin (MkCon n _ as _) = isLin n && all (not . isExplicit) as

||| True if the given constructor has name `(:<)` and
||| exactly two explicit arguments.
public export
isSnoc : Con n vs -> Bool
isSnoc (MkCon n _ as _) = isSnoc n && count isExplicit as == 2

||| True if the given type has a single constructor with a single
||| unerased argument.
public export
isNewtype : TypeInfo -> Bool
isNewtype (MkTypeInfo _ _ _ _ [c]) = count (not . isErased) c.args == 1
isNewtype _                      = False

||| True, if the given type has exactly one
||| `Nil` constructor with no explicit
||| argument and a `(::)` constructor with two explicit arguments.
public export
isListLike : TypeInfo -> Bool
isListLike (MkTypeInfo _ _ _ _ [x,y]) = isNil x && isCons y || isCons x && isNil y
isListLike _                        = False

||| True, if the given type has exactly one
||| `Lin` constructor with no explicit
||| argument and a `(:<)` constructor with two explicit arguments.
public export
isSnocListLike : TypeInfo -> Bool
isSnocListLike (MkTypeInfo _ _ _ _ [x,y]) =
  isLin x && isSnoc y || isSnoc x && isLin y
isSnocListLike _                        = False

||| True if the given type has a single constructor with only erased
||| arguments. Such a value will have a trivial runtime representation.
public export
isErased : TypeInfo -> Bool
isErased (MkTypeInfo _ _ _ _ [c]) = isConstant c
isErased _                        = False

||| Tries to get information about the data type specified
||| by name. The name need not be fully qualified, but
||| needs to be unambiguous.
export
getInfo' : Elaboration m => Name -> m TypeInfo
getInfo' n = do
  (n',tt)        <- lookupName n
  (args,IType _) <- pure $ unPi tt
    | (_,_) => fail "Type declaration does not end in IType: \{show tt}"

  let (arty ** vargs) := (length args ** Vect.fromList args)
  Just nargs    <- pure $ traverse name vargs
    | Nothing => fail "\{n'} has unnamed type arguments"
  conNames       <- getCons n'
  cons           <- traverse (getCon vargs) conNames
  pure (MkTypeInfo n' arty vargs nargs cons)

||| macro version of `getInfo'`
export %macro
getInfo : Name -> Elab TypeInfo
getInfo = getInfo'

||| Tries to get the name of the sole constructor
||| of data type specified by name. Fails, if
||| the name is not unambiguous, or if the data type
||| in question has not exactly one constructor.
export %macro
singleCon : Name -> Elab Name
singleCon n = do
  (MkTypeInfo _ _ _ _ [c]) <- getInfo' n
    | _ => fail "\{n} is not a single-constructor data type"
  pure $ c.name

--------------------------------------------------------------------------------
--          Parameterized Types
--------------------------------------------------------------------------------

public export
data ParamTag : Nat -> Type where
  I : ParamTag 0
  P : ParamTag 1

public export
data ParamPattern : (typeArgs, params : Nat) -> Type where
  Nil  : ParamPattern 0 0
  (::) : ParamTag k -> ParamPattern m n -> ParamPattern (S m) (k + n)

public export
paramsOnly : (k : Nat) -> ParamPattern k k
paramsOnly 0     = []
paramsOnly (S k) = P :: paramsOnly k

public export
indicesOnly : (k : Nat) -> ParamPattern k 0
indicesOnly 0     = []
indicesOnly (S k) = I :: indicesOnly k

public export
extractParams : ParamPattern n k -> (vs : Vect n a) -> Vect k a
extractParams []        []        = []
extractParams (I :: ps) (x :: xs) = extractParams ps xs
extractParams (P :: ps) (x :: xs) = x :: extractParams ps xs

||| Constructor argument type in a parameterized data type
||| with `n` parameters.
public export
data PArg : (n : Nat) -> Type where
  PPar      : Fin n -> PArg n
  PVar      : Name -> PArg n
  PLam      : Count -> PiInfo TTImp -> Maybe Name -> PArg n -> PArg n -> PArg n
  PApp      : (x,y : PArg n) -> PArg n
  PNamedApp : PArg n -> Name -> PArg n -> PArg n
  PAutoApp  : PArg n -> PArg n -> PArg n
  PWithApp  : PArg n -> PArg n -> PArg n
  PSearch   : Nat -> PArg n
  PPrim     : Constant -> PArg n
  PDelayed  : LazyReason -> PArg n -> PArg n
  PType     : PArg n
  PHole     : String -> PArg n

||| Checks if two `PArgs` are equal (ignoring the `FC`).
export
Eq (PArg n) where
  PPar x == PPar y = x == y
  PVar x == PVar y = x == y
  PApp x y == PApp v w = x == v && y == w
  PLam c p m u v == PLam d q n x y =
    c == d && p == q && m == n && u == x && v == y
  PNamedApp x m y == PNamedApp v n w = x == v && m == n && y == w
  PAutoApp x y == PAutoApp v w = x == v && y == w
  PWithApp x y == PWithApp v w = x == v && y == w
  PSearch c == PSearch d = c == d
  PPrim c == PPrim d = c == d
  PDelayed lr x == PDelayed lr2 y = lr == lr2 && x == y
  PType == PType = True
  PHole c == PHole d = c == d
  _ == _ = False

||| Checks if the given name corresponds to a parameter, in
||| which case it must be present in the given vector of names.
public export
pvar : Named a => Vect n a -> (bound : List Name) -> Name -> PArg n
pvar xs bound nm = case findIndex (\v => nm == v.getName) xs of
  Just ix => if nm `elem` bound then PVar nm else PPar ix
  Nothing => PVar nm

||| Tries to convert a `TTImp` to an argument of a
||| parameterized constructor using the given vector of parameter names.
public export
parg : Named a => Vect n a -> (bound : List Name) -> TTImp -> Res (PArg n)
parg xs b (IVar _ nm)         = Right $ pvar xs b nm
parg xs b (IApp _ s t)        = PApp <$> parg xs b s <*> parg xs b t
parg xs b (INamedApp _ s n t) = PNamedApp <$> parg xs b s <*> pure n <*> parg xs b t
parg xs b (IAutoApp _ s t)    = PAutoApp <$> parg xs b s <*> parg xs b t
parg xs b (IWithApp _ s t)    = PWithApp <$> parg xs b s <*> parg xs b t
parg xs b (IDelayed _ lr s)   = PDelayed lr <$> parg xs b s
parg xs b (IPrimVal _ c)      = Right $ PPrim c
parg xs b (IType _)           = Right PType
parg xs b (ISearch _ n)       = Right $ PSearch n
parg xs b (IHole _ n)         = Right $ PHole n
parg xs b (ILam _ c p n x y)  =
  [| PLam (pure c) (pure p) (pure n) (parg xs b x) (parg xs (toList n ++ b) y) |]
parg xs b t                 =
  Left "\{show t} is not a valid constructor argument type"

namespace PArg
  ||| Converts an argument of a parameterized data type to the
  ||| corresponding `TTImp` expression.
  public export
  ttimp : Vect n Name -> PArg n -> TTImp
  ttimp ns (PPar x)          = var (index x ns)
  ttimp ns (PVar nm)         = var nm
  ttimp ns (PApp x y)        = ttimp ns x `app` ttimp ns y
  ttimp ns (PNamedApp x n y) = INamedApp EmptyFC (ttimp ns x) n (ttimp ns y)
  ttimp ns (PAutoApp x y)    = IAutoApp EmptyFC (ttimp ns x) (ttimp ns y)
  ttimp ns (PWithApp x y)    = IWithApp EmptyFC (ttimp ns x) (ttimp ns y)
  ttimp ns (PPrim c)         = primVal c
  ttimp ns (PDelayed lr x)   = IDelayed EmptyFC lr (ttimp ns x)
  ttimp ns (PSearch n)       = ISearch EmptyFC n
  ttimp ns PType             = IType EmptyFC
  ttimp ns (PHole n)         = IHole EmptyFC n
  ttimp ns (PLam c p n x y)  = ILam EmptyFC c p n (ttimp ns x) (ttimp ns y)

||| Extracts the sub-expressions from an argument's type
||| where the outermost value is a parameter.
|||
||| Example:
||| If `f`, `a`, and `b` are parameters, this will extract
||| `[f Int, f a, b]` from `Maybe (Pair (f Int, Pair (f a, b)))`
public export
paramArgs : PArg n -> List (PArg n)
paramArgs (PPar x)                   = [PPar x]
paramArgs (PVar nm)                  = []
paramArgs p@(PApp (PPar _) y)        = [p]
paramArgs p@(PAutoApp (PPar _) y)    = [p]
paramArgs p@(PWithApp (PPar _) y)    = [p]
paramArgs p@(PNamedApp (PPar _) n y) = [p]
paramArgs (PLam _ _ _ _ y)           = paramArgs y
paramArgs (PApp x y)                 = nub $ paramArgs x ++ paramArgs y
paramArgs (PAutoApp x y)             = nub $ paramArgs x ++ paramArgs y
paramArgs (PWithApp x y)             = nub $ paramArgs x ++ paramArgs y
paramArgs (PNamedApp x n y)          = nub $ paramArgs x ++ paramArgs y
paramArgs (PPrim c)                  = []
paramArgs (PDelayed lr x)            = paramArgs x
paramArgs  PType                     = []
paramArgs (PSearch _)                = []
paramArgs (PHole _)                  = []

public export
paramNames :
     {0 vs : Vect n Arg}
  -> ParamPattern n k
  -> AppArgs vs
  -> Res (Vect k Name)
paramNames []        []        = Right []
paramNames (I :: ps) (v :: vs) = paramNames ps vs
paramNames (P :: ps) (v :: vs) = case v.ttimp of
  IVar _ nm => (nm ::) <$> paramNames ps vs
  t         => Left "\{show t} is not a parameter"

||| Argument of a data constructor of a parameterized data type.
public export
data ConArg : (n : Nat) -> Type where
  ParamArg : Fin n -> TTImp -> ConArg n
  CArg     : Maybe Name -> Count -> PiInfo TTImp -> PArg n -> ConArg n

public export
isExplicit : ConArg n -> Bool
isExplicit (CArg mnm rig ExplicitArg x) = True
isExplicit _                            = False

public export
conArg : Vect n Name -> Arg -> Res (ConArg n)
conArg ns (MkArg M0 ImplicitArg (Just nm) t) = case findIndex (nm ==) ns of
  Just ix => Right $ ParamArg ix t
  Nothing => CArg (Just nm) M0 ImplicitArg <$> parg ns Nil t
conArg ns (MkArg c pi nm t)                  = CArg nm c pi <$> parg ns Nil t

namespace ConArg
  public export
  paramArgs : ConArg n -> List (PArg n)
  paramArgs (ParamArg _ _) = []
  paramArgs (CArg _ _ _ t) = paramArgs t

public export
record ParamCon (n : Nat) where
  constructor MkParamCon
  name : Name
  arty : Nat
  args : Vect arty (ConArg n)

namespace ParamCon
  public export
  paramArgs : ParamCon n -> List (PArg n)
  paramArgs c = nub $ toList c.args >>= paramArgs

public export
Named (ParamCon n) where
  c.getName = c.name

public export
paramCon : ParamPattern n k -> Con n vs -> Res (ParamCon k)
paramCon ps (MkCon name arty args typeArgs) = do
  params  <- paramNames ps typeArgs
  conArgs <- traverse (conArg params) args
  pure $ MkParamCon name arty conArgs

public export
record ParamTypeInfo where
  constructor MkParamTypeInfo
  ||| Underlying type info
  info       : TypeInfo

  ||| Information about which type arguments are parameters and
  ||| which are indices
  pattern    : ParamPattern info.arty numParams

  ||| Name of parameters
  paramNames : Vect numParams Name

  ||| List of data constructors
  cons       : List (ParamCon numParams)

  ||| List of types appearing in constructor arguments, where the
  ||| the outermost applied type is one of the parameters. We use this
  ||| to generate the constraints necessary to implement interfaces such
  ||| as `Eq` or `Ord`.
  |||
  ||| For instance, in case of a constructor argument `Either (f a) (b, f Nat)`
  ||| with `f`, `a`, and `b` being parameters, this list will contain
  ||| the encoded forms of `f a`, `f Nat`, and `b`.
  pargs      : List (PArg numParams)

public export
Named ParamTypeInfo where
  p.getName = p.info.name

public export
paramType : (ti : TypeInfo) -> ParamPattern ti.arty k -> Res ParamTypeInfo
paramType ti@(MkTypeInfo nm n vs ns cs) ps = do
  cons <- traverse (paramCon ps) cs
  pure $ MkParamTypeInfo ti ps (extractParams ps ns) cons (nub $ cons >>= paramArgs)

||| Returns the constraints required to implement the given interface
||| for the given parameterized data types.
|||
||| The interface must be of type `Type -> Type`.
export
constraints : ParamTypeInfo -> (iname : Name) -> List Arg
constraints p iname = map (toCon p.paramNames) p.pargs
  where toCon : Vect k Name ->  PArg k -> Arg
        toCon ns pa = MkArg MW AutoImplicit Nothing . (app $ var iname) $
                   ttimp ns pa

namespace ParamTypeInfo
  ||| Returns the type constructor of a parameterized
  ||| data type applied to its parameters
  public export
  (.applied) : ParamTypeInfo -> TTImp
  (.applied) p = p.info.applied

  ||| Returns a list of implicit arguments corresponding
  ||| to the data type's arguments.
  public export %inline
  (.implicits) : ParamTypeInfo -> List Arg
  (.implicits) p = p.info.implicits

||| Short-hand for `p.implicits ++ constraints iname p`.
public export %inline
allImplicits : (p : ParamTypeInfo) -> (iname : Name) -> List Arg
allImplicits p iname = p.implicits ++ constraints p iname

||| Returns information about a parameterized data type
||| specified by the given (probably not fully qualified) name
||| and a strategy for distinguishing between type parameters
||| and indices.
export
getParamInfo' :
    {auto _ : Elaboration m}
  -> Name
  -> m ParamTypeInfo
getParamInfo' n = do
  ti <- getInfo' n
  case paramType ti (paramsOnly ti.arty) of
    Right pt => pure pt
    Left err => fail "Type \{n} is not supported: \{err}"

||| macro version of `getParamInfo`.
export %macro
getParamInfo : Name -> Elab ParamTypeInfo
getParamInfo = getParamInfo'

