module Language.Reflection.Types

-- inspired by https://github.com/MarcelineVQ/idris2-elab-deriving/

import public Language.Reflection.Syntax
import public Language.Reflection
import public Data.Vect.Quantifiers
import public Data.Vect

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
freshNames : String -> (n : Nat) -> Vect n Name
freshNames s = go 0
  where go : Nat -> (k : Nat) -> Vect k Name
        go m 0     = []
        go m (S k) = UN (Basic $ s ++ show m) :: go (S m) k

public export
implicits : Foldable t => t Name -> List Arg
implicits = map erasedImplicit . toList

||| Tries to generate the given proofs for all values in the
||| given vector over an applicative functor.
public export
tryAll :
     {0 a : Type}
  -> {0 p : a -> Type}
  -> Applicative f
  => ((v : a) -> f (p v))
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
||| We use these to match applied constructor types against the
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
(.ttimp) : AppArg (MkArg c ExplicitArg n t) -> TTImp
(.ttimp) (NamedApp nm s) = s
(.ttimp) (Regular s)     = s
(.ttimp) (Missing x)     = absurd x

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
  unappVia $ \case INamedApp fc t nm u =>
                     if n == nm then Just (NamedApp n u, t) else Nothing
                   _                   => Nothing

-- tries to extract an auto-implicit argument from an expression
getAuto : TTImp -> Maybe (AppArg (MkArg c AutoImplicit n t), TTImp)
getAuto = unappVia $ \case IAutoApp fc t u => Just (AutoApp u, t)
                           _               => Nothing

-- tries to extract a regular argument from an expression
regular : TTImp -> Maybe (AppArg (MkArg c ExplicitArg n t), TTImp)
regular = unappVia $ \case IApp fc t u => Just (Regular u, t)
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
bindCon : (c : Con n vs) -> Vect c.arty Name -> TTImp
bindCon c ns = go c.nameVar (map piInfo c.args) ns
  where go : TTImp -> Vect k (PiInfo TTImp) -> Vect k Name -> TTImp
        go t []                  []        = t
        go t (ExplicitArg :: xs) (n :: ns) = go (t .$ n.bindVar) xs ns
        go t (_           :: xs) (n :: ns) = go t xs ns

||| Applies a constructor to variables of the given name.
export
applyCon : (c : Con n vs) -> Vect c.arty Name -> TTImp
applyCon c ns = go c.nameVar (map piInfo c.args) ns
  where go : TTImp -> Vect k (PiInfo TTImp) -> Vect k Name -> TTImp
        go t []                  []        = t
        go t (ExplicitArg :: xs) (n :: ns) = go (t .$ var n) xs ns
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
  name : Name
  arty : Nat
  args : Vect arty Arg
  cons : List (Con arty args)

public export %inline
Named TypeInfo where
  t.getName = t.name

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
isNewtype (MkTypeInfo _ _ _ [c]) = count (not . isErased) c.args == 1
isNewtype _                      = False

||| True, if the given type has exactly one
||| `Nil` constructor with no explicit
||| argument and a `(::)` constructor with two explicit arguments.
public export
isListLike : TypeInfo -> Bool
isListLike (MkTypeInfo _ _ _ [x,y]) = isNil x && isCons y || isCons x && isNil y
isListLike _                        = False

||| True, if the given type has exactly one
||| `Lin` constructor with no explicit
||| argument and a `(:<)` constructor with two explicit arguments.
public export
isSnocListLike : TypeInfo -> Bool
isSnocListLike (MkTypeInfo _ _ _ [x,y]) =
  isLin x && isSnoc y || isSnoc x && isLin y
isSnocListLike _                        = False

||| True if the given type has a single constructor with only erased
||| arguments. Such a value will have a trivial runtime representation.
public export
isErased : TypeInfo -> Bool
isErased (MkTypeInfo _ _ _ [c]) = isConstant c
isErased _                      = False

||| Tries to get information about the data type specified
||| by name. The name need not be fully qualified, but
||| needs to be unambiguous.
export
getInfo' : Elaboration m => Name -> m TypeInfo
getInfo' n =
  do (n',tt)        <- lookupName n
     (args,IType _) <- pure $ unPi tt
       | (_,_) => fail "Type declaration does not end in IType: \{show tt}"

     let (arty ** vargs) := (length args ** Vect.fromList args)

     conNames       <- getCons n'
     cons           <- traverse (getCon vargs) conNames
     pure (MkTypeInfo n' arty vargs cons)

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
  (MkTypeInfo _ _ _ cs) <- getInfo' n
  (c::Nil) <- pure cs | _ => fail "not a single constructor"
  pure $ c.name

--------------------------------------------------------------------------------
--          Parameterized Types
--------------------------------------------------------------------------------

||| Witness that a `TTImp` expression is a
||| basic type level function similar to Haskell 98's kind system.
|||
||| For parameterized data types, we only accept type arguments of this
||| shape.
public export
data Tpe : TTImp -> Type where
  Ty  : Tpe (IType fc)
  Pi  : Tpe x -> Tpe y -> Tpe (IPi fc c ExplicitArg nm x y)
  Hol : Tpe (IHole fc s)

||| Tries to convert a `TTImp` to a `Tpe` without loss of information.
public export
tpe : (t : TTImp) -> Res (Tpe t)
tpe (IType fc)                    = Right Ty
tpe (IPi fc c ExplicitArg nm x y) = Pi <$> tpe x <*> tpe y
tpe (IHole fc s)                  = Right Hol
tpe t                             =
  Left "\{show t} is not a simple type argument"

||| Proof that the given argument has the shape of a parameter in a
||| parameterized data type.
public export
data Param : Arg -> Type where
  IsParam : Tpe t -> Param (MkArg c ExplicitArg nm t)

||| Proof that the given type arguments have the shape of a
||| parameter in a parameterized data type.
public export
0 Params : Vect n Arg -> Type
Params = All Param

||| Tries to proof that the type argument is a plain type or type function.
public export
param : (a : Arg) -> Res (Param a)
param (MkArg c ExplicitArg nm t) = IsParam <$> tpe t
param (MkArg _ _           nm t) =
  let str := maybe "_" show nm
   in Left "\{str} is not an explicit type argument"

||| Constructor argument type in a parameterized data type
||| with `n` parameters.
public export
data PArg : (n : Nat) -> Type where
  PPar     : FC -> Fin n -> PArg n
  PVar     : FC -> Name -> PArg n
  PApp     : FC -> (x,y : PArg n) -> PArg n
  PPrim    : FC -> Constant -> PArg n
  PDelayed : FC -> LazyReason -> PArg n -> PArg n
  PType    : FC -> PArg n

||| Checks if two `PArgs` are equal (ignoring the `FC`).
export
Eq (PArg n) where
  PPar _ x        == PPar _ y         = x == y
  PVar _ x        == PVar _ y         = x == y
  PApp _ x y      == PApp _ v w       = x == v && y == w
  PPrim _ c       == PPrim _ d        = c == d
  PDelayed _ lr x == PDelayed _ lr2 y = lr == lr2 && x == y
  PType _         == PType _          = True
  _               == _                = False

||| Checks if the given name corresponds to a parameter, in
||| which case it must be present in the given vector of names.
public export
pvar : Named a => Vect n a -> FC -> Name -> PArg n
pvar xs fc nm = case findIndex (\v => nm == v.getName) xs of
  Just ix => PPar fc ix
  Nothing => PVar fc nm

||| Tries to convert a `TTImp` to an argument of a
||| parameterized constructor using the given vector of parameter names.
public export
parg : Named a => Vect n a -> TTImp -> Res (PArg n)
parg xs (IVar fc nm)       = Right $ pvar xs fc nm
parg xs (IApp fc s t)      = PApp fc <$> parg xs s <*> parg xs t
parg xs (IDelayed fc lr s) = PDelayed fc lr <$> parg xs s
parg xs (IPrimVal fc c)    = Right $ PPrim fc c
parg xs (IType fc)         = Right $ PType fc
parg xs t                  =
  Left "\{show t} is not a valid constructor argument type"

namespace PArg
  ||| Converts an argument of a parameterized data type to the
  ||| corresponding `TTImp` expression.
  public export
  ttimp : Vect n Name -> PArg n -> TTImp
  ttimp ns (PPar fc x)        = IVar fc (index x ns)
  ttimp ns (PVar fc nm)       = IVar fc nm
  ttimp ns (PApp fc x y)      = IApp fc (ttimp ns x) (ttimp ns y)
  ttimp ns (PPrim fc c)       = IPrimVal fc c
  ttimp ns (PDelayed fc lr x) = IDelayed fc lr (ttimp ns x)
  ttimp ns (PType fc)         = IType fc

||| Extracts the sub-expressions from an argument's type
||| where the outermost value is a parameter.
|||
||| Example:
||| If `f`, `a`, and `b` are parameters, this will extract
||| `[f Int, f a, b]` from `Maybe (Pair (f Int, Pair (f a, b)))`
public export
paramArgs : PArg n -> List (PArg n)
paramArgs (PPar fc x)              = [PPar fc x]
paramArgs (PVar fc nm)             = []
paramArgs p@(PApp fc (PPar _ _) y) = [p]
paramArgs (PApp fc x y)            = nub $ paramArgs x ++ paramArgs y
paramArgs (PPrim fc c)             = []
paramArgs (PDelayed fc lr x)       = paramArgs x
paramArgs (PType fc)               = []

public export
paramNames : {0 vs : Vect n Arg} -> Params vs -> AppArgs vs -> Res (Vect n Name)
paramNames []                []        = Right []
paramNames (IsParam _ :: ps) (v :: vs) = case v.ttimp of
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
  Nothing => CArg (Just nm) M0 ImplicitArg <$> parg ns t
conArg ns (MkArg c pi nm t)           = CArg nm c pi <$> parg ns t

namespace ConArg
  public export
  paramArgs : ConArg n -> List (PArg n)
  paramArgs (ParamArg _ _) = []
  paramArgs (CArg _ _ _ t) = paramArgs t

public export
record ParamCon (n : Nat) where
  constructor MkParamCon
  name       : Name
  arty       : Nat
  args       : Vect arty (ConArg n)
  paramNames : Vect n Name

namespace ParamCon
  public export
  paramArgs : ParamCon n -> List (PArg n)
  paramArgs c = nub $ toList c.args >>= paramArgs

public export
Named (ParamCon n) where
  c.getName = c.name

public export
paramCon : Params vs -> Con n vs -> Res (ParamCon n)
paramCon ps (MkCon name arty args typeArgs) = do
  params  <- paramNames ps typeArgs
  conArgs <- traverse (conArg params) args
  pure $ MkParamCon name arty conArgs params

public export
record ParamTypeInfo where
  constructor MkParamTypeInfo
  ||| Underlying type info
  info       : TypeInfo

  ||| Witness that all type arguments of the type constructor
  ||| are basic type-level functions as defined in `Tpe t`.
  params     : Params info.args

  ||| Default parameter names. These are either the explicitly
  ||| given names or the names used in the first data constructor
  ||| for unnamed parameters. Generated names are used for
  ||| the rare zero-constructor data types with unnamed parameters.
  defltNames : Vect info.arty Name

  ||| List of data constructors
  cons       : List (ParamCon info.arty)

  ||| List of types appearing in constructor arguments, where the
  ||| the outermost applied type is one of the parameters. We use this
  ||| to generate the constraints necessary to implement interfaces such
  ||| as `Eq` or `Ord`.
  |||
  ||| For instance, in case of a constructor argument `Either (f a) (b, f Nat)`
  ||| with `f`, `a`, and `b` being parameters, this list will contain
  ||| the encoded forms of `f a`, `f Nat`, and `b`.
  pargs      : List (PArg info.arty)

public export
Named ParamTypeInfo where
  p.getName = p.info.name

public export
paramType : TypeInfo -> Res ParamTypeInfo
paramType ti@(MkTypeInfo nm n vs cs) = do
  ps     <- tryAll param vs
  cons   <- traverse (paramCon ps) cs

  let names := case cons of
                 h :: _ => h.paramNames
                 Nil    => freshNames "par" n

      pns   := zipWith (\a,n => fromMaybe n a.name) vs names

  pure $ MkParamTypeInfo ti ps pns cons (nub $ cons >>= paramArgs)

||| Returns the constraints required to implement the given interface
||| for the given parameterized data types.
|||
||| The interface must be of type `Type -> Type`.
export
constraints : ParamTypeInfo -> (iname  : Name) -> List Arg
constraints p iname = map toCon p.pargs
  where toCon : PArg p.info.arty -> Arg
        toCon pa = MkArg MW AutoImplicit Nothing . (var iname .$) $
                   ttimp p.defltNames pa

||| Returns the type constructor of a parameterized
||| data type applied to its parameters
public export
(.applied) : ParamTypeInfo -> TTImp
(.applied) p = appArgs p.getName p.defltNames

||| Returns a list of implicit arguments corresponding
||| to the data type's parameters.
public export %inline
(.implicits) : ParamTypeInfo -> List Arg
(.implicits) p = implicits p.defltNames

||| Short-hand for `p.implicits ++ constraints iname p`.
public export %inline
allImplicits : (p : ParamTypeInfo) -> (iname : Name) -> List Arg
allImplicits p iname = p.implicits ++ constraints p iname

||| Returns information about a parameterized data type
||| specified by the given (probably not fully qualified) name.
|||
||| The implementation makes sure, that all occurences of
||| type parameters in the constructors have been given
||| the same names as occurences in the type declaration.
export
getParamInfo' : Elaboration m => Name -> m ParamTypeInfo
getParamInfo' n = do
  ti <- getInfo' n
  case paramType ti of
    Right pt => pure pt
    Left err => fail "\{n} is not a parameterized type: \{err}"

||| macro version of `getParamInfo`.
export %macro
getParamInfo : Name -> Elab ParamTypeInfo
getParamInfo = getParamInfo'

-- ||| Information about a parameterized data type.
-- |||
-- ||| The constructors of such a data type are only
-- ||| allowed to have two kinds of arguments:
-- ||| Implicit arguments corresponding to the data
-- ||| type's parameters and explicit arguments.
-- |||
-- ||| Auto implicits or existentials are not allowed.
-- |||
-- ||| Below are some examples of valid parameterized data types
-- |||
-- ||| ```
-- ||| data Foo a = Val a | Nope
-- |||
-- ||| data Reader : (m : Type -> Type) -> (e : Type) -> (a : Type) -> Type where
-- |||   MkReader : (run : e -> m a) -> Reader m e a
-- |||
-- ||| data Wrapper : (n : Nat) -> (t : Type) -> Type
-- |||   Wrap : Vect n t -> Wrapper n t
-- ||| ```
-- |||
-- ||| Examples of invalid parameterized data types
-- |||
-- ||| Indexed types families:
-- |||
-- ||| ```
-- ||| data GADT : (t : Type) -> Type where
-- |||   A : GADT Int
-- |||   B : GADT ()
-- |||   Any : a -> GADT a
-- ||| ```
-- |||
-- ||| Existentials:
-- |||
-- ||| ```
-- ||| data Forget : Type where
-- |||  DoForget : a -> Forget
-- ||| ```
-- |||
-- ||| Constraint types:
-- |||
-- ||| ```
-- ||| data ShowableForget : Type where
-- |||  ShowForget : Show a => a -> Forget
-- ||| ```
-- public export
-- record ParamTypeInfo where
--   constructor MkParamTypeInfo
--   name   : Name
--   params : List (Name,TTImp)
--   cons   : List ParamCon
--
-- public export %inline
-- Named ParamTypeInfo where
--   t.getName = t.name
