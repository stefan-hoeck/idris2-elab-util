||| Some utilities for defining and manipulating TTImp values
||| for writing elaborator scripts.
|||
||| Some notes: Use quotes whenever possible:
|||
||| Names can be quoted like so: `{ AName }, `{ In.Namespace.AName }.
||| Both examples are of type Language.Reflection.TT.Name.
|||
||| Expressions can be quoted like so: `(\x => x * x)
module Language.Reflection.Syntax

import Data.String
import Data.List1
import Language.Reflection

%default total

--------------------------------------------------------------------------------
--          Names
--------------------------------------------------------------------------------

public export
FromString Name where
  fromString s = run (split ('.' ==) s) []

    where
      run : List1 String -> List String -> Name
      run (h ::: []) []        = UN $ Basic h
      run (h ::: []) ns        = NS (MkNS ns) (UN $ Basic h)
      run ll@(h ::: (y :: ys)) xs =
        run (assert_smaller ll $ y ::: ys) (h :: xs)

export
Interpolation Name where
  interpolate = show

||| True if the given name ends on (`Basic $ UN "Nil")
public export
isNil : Name -> Bool
isNil (NS ns nm)         = isNil nm
isNil (UN $ Basic "Nil") = True
isNil _                  = False

||| True if the given name ends on (`Basic $ UN "Lin")
public export
isLin : Name -> Bool
isLin (NS ns nm)         = isLin nm
isLin (UN $ Basic "Lin") = True
isLin _                  = False

||| True if the given name ends on (`Basic $ UN "::")
public export
isCons : Name -> Bool
isCons (NS ns nm)        = isCons nm
isCons (UN $ Basic "::") = True
isCons _                 = False

||| True if the given name ends on (`Basic $ UN ":<")
public export
isSnoc : Name -> Bool
isSnoc (NS ns nm)        = isSnoc nm
isSnoc (UN $ Basic ":<") = True
isSnoc _                 = False

||| Takes a (probably fully qualified name) and generates a
||| identifier from this without the dots.
|||
||| Example : camelCase "Data.List1.List1" = "DataList1List1"
export
camelCase : Name -> String
camelCase = concat . split ('.' ==) . show

||| Convert a `Name` to a simple string dropping some of its context
||| like its namespace (if any).
|||
||| Use this to get access to a simple variable name or to print the
||| un-prefixed name of a data- or type constructor.
export
nameStr : Name -> String
nameStr (UN $ Basic x)  = x
nameStr (UN $ Field x)  = x
nameStr (UN Underscore) = "_"
nameStr (NS _ x) = nameStr x
nameStr (MN x y) = x ++ show y
nameStr (DN _ x) = nameStr x
nameStr (Nested (x,y) n) = #"nested_\#{nameStr n}_\#{show x}_\#{show y}"#
nameStr (CaseBlock x n) = #"case_n_\#{show x}"#
nameStr (WithBlock x n) = #"with_n_\#{show x}"#

||| An interface for things with a `Name`.
|||
||| This comes with several utility function strewn across this module
||| for creating variables from names and printing a name as a string.
||| All these make use of dot syntax, so they can be used like record
||| projections.
public export
interface Named a where
  ||| Extract the `Name` from a value.
  |||
  ||| We call this `(.getName)` instead
  ||| of just `(.name)`, because `name` is a commonly used record field name.
  (.getName) : a -> Name

public export %inline
Named Name where
  n.getName = n

||| Use `nameStr` to convert the name of a value to a simple string.
public export %inline
(.nameStr) : Named a => a -> String
x.nameStr = nameStr x.getName

--------------------------------------------------------------------------------
--          Vars
--------------------------------------------------------------------------------

||| Creates a variable from the given name
|||
||| Names are best created using quotes: `{ AName },
||| `{ In.Namespacs.Name }.
|||
||| Likewise, if the name is already known at the time of
||| writing, use quotes for defining variables directly: `(AName)
public export %inline
var : (name : Name) -> TTImp
var = IVar EmptyFC

||| Creates a variable with the name of the given value.
public export %inline
(.nameVar) : Named a => a -> TTImp
n.nameVar = var n.getName

||| Alias for `var . fromString`
public export %inline
varStr : String -> TTImp
varStr = var . fromString

||| Binds a new variable, for instance in a pattern match.
|||
||| This is an alias for `IBindVar EmptyFC`.
public export %inline
bindVar : String -> TTImp
bindVar = IBindVar EmptyFC

||| Bind a named value to a variable. This uses `nameStr` for
||| the variable's name.
public export %inline
(.bindVar) : Named a => a -> TTImp
x.bindVar = bindVar x.nameStr

||| Implicit value bound if unsolved
|||
||| This is an alias for `Implicit EmptyFC True`
public export %inline
implicitTrue : TTImp
implicitTrue = Implicit EmptyFC True

||| Implicitly typed value unbound if unsolved
|||
||| This is an alias for `Implicit EmptyFC False`
public export %inline
implicitFalse : TTImp
implicitFalse = Implicit EmptyFC False

||| Primitive values.
|||
||| This is an alias for `IPrimVal EmptyFC`
public export %inline
primVal : (c : Constant) -> TTImp
primVal = IPrimVal EmptyFC

||| Creates a string constant from a named value. Uses
||| `nameStr` to convert the name to a string.
public export %inline
(.namePrim) : Named a => a -> TTImp
x.namePrim = primVal $ Str x.nameStr

||| The type `Type`.
|||
||| This is an alias for `IType EmptyFC`.
public export %inline
type :  TTImp
type = IType EmptyFC

||| A named hole.
|||
||| This is an alias for `IHole EmptyFC`.
public export %inline
hole :  String -> TTImp
hole = IHole EmptyFC

||| Tries to extract a variable name from a `TTImp`.
|||
||| Returns `Nothing` if not an `IVar`.
public export
unVar : TTImp -> Maybe Name
unVar (IVar _ n) = Just n
unVar _          = Nothing

||| Proof search
|||
||| This is an alias for `ISearch EmptyFC`
public export %inline
iSearch : (depth : Nat) -> TTImp
iSearch = ISearch EmptyFC

--------------------------------------------------------------------------------
--          Application
--------------------------------------------------------------------------------

||| Function application.
|||
||| This is an alias for `IApp EmptyFC`.
|||
||| Example: ```app (var "Just") (var "x")```
|||          is equivalent to `(Just x)
public export %inline
app : (fun, arg : TTImp) -> TTImp
app = IApp EmptyFC

export
unApp : TTImp -> (TTImp,List TTImp)
unApp = run []

  where
    run : List TTImp -> TTImp -> (TTImp,List TTImp)
    run xs (IApp _ y z) = run (z :: xs) y
    run xs t            = (t,xs)

||| Applies a list of variables to a function.
|||
||| See `appNames` for an example
public export %inline
appAll : Name -> List TTImp -> TTImp
appAll fun = foldl app (var fun)

||| Applies a list of variable names to a function.
|||
||| Example: appNames "either" ["f","g","val"]
|||          is equivalent to ~(either f g val)
public export %inline
appNames : (fun : Name) -> (args : List Name) -> TTImp
appNames fun = appAll fun . map var

||| Binds a list of parameters to a data constructor in
||| a pattern match.
|||
||| Example: bindAll "MkPair" ["a","b"]
|||          is the same as `(MkPair a b)
public export %inline
bindAll : (fun : Name) -> (args : List String) -> TTImp
bindAll fun = appAll fun . map bindVar

||| Alias for `IBindHere EmptyFC`
public export %inline
bindHere : (mode : BindMode) -> (val : TTImp) -> TTImp
bindHere = IBindHere EmptyFC

||| Alias for `IMustUnify EmptyFC`
public export %inline
mustUnify : (reason : DotReason) -> (val : TTImp) -> TTImp
mustUnify = IMustUnify EmptyFC

||| Alias for `IAs EmptyFC EmptyFC`
public export %inline
iAs : (side : UseSide) -> (name : Name) -> (val : TTImp) -> TTImp
iAs = IAs EmptyFC EmptyFC

||| Applying an auto-implicit.
|||
||| This is an alias for `IAutoApp EmptyFC`.
|||
||| Example: `autoApp (var "traverse") (var "MyApp")`
|||          is equivalent to `(traverse @{MyApp})
public export %inline
autoApp : (fun, arg : TTImp) -> TTImp
autoApp = IAutoApp EmptyFC

||| Infix version of `autoApp`
public export %inline
(.@) : TTImp -> TTImp -> TTImp
(.@) = autoApp

||| Application in a `with` expression
|||
||| This is an alias for `IWithApp EmptyFC`.
public export %inline
withApp : (fun, arg : TTImp) -> TTImp
withApp = IWithApp EmptyFC

||| Named function application.
|||
||| This is an alias for `INamedApp EmptyFC`.
|||
||| Example: `namedApp (var "traverse") "f" (var "MyApp")`
|||          is equivalent to `(traverse {f = MyApp})
public export %inline
namedApp : (fun : TTImp) -> (name : Name) -> (arg : TTImp) -> TTImp
namedApp = INamedApp EmptyFC

||| Catch-all pattern match on a data constructor.
|||
||| Example: `bindAny "Person"`
|||          is the same as `(Person {})
||| ```
public export %inline
bindAny : Named a => a -> TTImp
bindAny n = namedApp n.nameVar (UN Underscore) implicitTrue

||| Alias for `IAlternative EmptyFC`
public export %inline
alternative : (tpe : AltType) -> (alts : List TTImp) -> TTImp
alternative = IAlternative EmptyFC

--------------------------------------------------------------------------------
--          Function Arguments
--------------------------------------------------------------------------------

||| A function argument, typically extracted from pi-types or used
||| to define pi-types.
public export
record Arg where
  constructor MkArg
  count  : Count
  piInfo : PiInfo TTImp
  name   : Maybe Name
  type   : TTImp

||| Creates an explicit unnamed argument of the given type.
public export %inline
arg : TTImp -> Arg
arg = MkArg MW ExplicitArg Nothing

||| Creates an explicit, unnamed, zero-quantity
||| argument of the given type.
public export %inline
erasedArg : TTImp -> Arg
erasedArg = MkArg M0 ExplicitArg Nothing

||| Creates an explicit argument of the given name
||| to be used in a lambda.
public export %inline
lambdaArg : Named a => a -> Arg
lambdaArg n = MkArg MW ExplicitArg (Just n.getName) implicitFalse

||| Creates an erased implicit argument of the given name.
public export %inline
erasedImplicit : Named a => a -> Arg
erasedImplicit n = MkArg M0 ImplicitArg (Just n.getName) implicitFalse

||| True if the given argument is an explicit argument.
public export
isExplicit : Arg -> Bool
isExplicit (MkArg _ ExplicitArg _ _) = True
isExplicit (MkArg _ _           _ _) = False

||| True if the given argument has quantity zero.
public export
isErased : Arg -> Bool
isErased (MkArg M0 _ _ _) = True
isErased _                = False

||| True if the given argument is explicit and does not have
||| quantity zero.
public export
isExplicitUnerased : Arg -> Bool
isExplicitUnerased (MkArg M1 ExplicitArg _ _) = True
isExplicitUnerased (MkArg MW ExplicitArg _ _) = True
isExplicitUnerased _                          = False

||| Extracts the arguments from a function type.
export
unPi : TTImp -> (List Arg, TTImp)
unPi (IPi _ c p n at rt) = mapFst (MkArg c p n at ::) $ unPi rt
unPi tpe                 = ([],tpe)

||| Extracts the arguments from a lambda.
export
unLambda : TTImp -> (List Arg, TTImp)
unLambda (ILam _ c p n at rt) = mapFst (MkArg c p n at ::) $ unLambda rt
unLambda tpe                  = ([],tpe)

--------------------------------------------------------------------------------
--          Lambdas
--------------------------------------------------------------------------------

||| Defines an anonymous function (lambda).
|||
||| This passes the fields of `Arg` to `ILam EmptyFC`
public export
lam : (arg : Arg) -> (lamTy : TTImp) -> TTImp
lam (MkArg c p n t) = ILam EmptyFC c p n t

--------------------------------------------------------------------------------
--          Function Types
--------------------------------------------------------------------------------

||| Defines a function type.
|||
||| This passes the fields of `Arg` to `IPi EmptyFC`
public export
pi : (arg : Arg) -> (retTy : TTImp) -> TTImp
pi (MkArg c p n t) = IPi EmptyFC c p n t

||| Defines a function type taking the given arguments.
public export %inline
piAll : TTImp -> List Arg -> TTImp
piAll res = foldr pi res

||| Defines a function type taking implicit arguments of the
||| given names.
public export %inline
piAllImplicit : TTImp -> List Name -> TTImp
piAllImplicit res = piAll res . map erasedImplicit

||| Defines a function type taking the given auto-implicit arguments.
public export
piAllAuto : TTImp -> List TTImp -> TTImp
piAllAuto res = piAll res . map (MkArg MW AutoImplicit Nothing)

--------------------------------------------------------------------------------
--          Pattern Matching
--------------------------------------------------------------------------------

||| An impossible clause in a pattern match.
|||
||| This is an alias for `ImpossibleClause EmptyFC`.
public export %inline
impossibleClause : (lhs : TTImp) -> Clause
impossibleClause = ImpossibleClause EmptyFC

||| A pattern clause consisting of the left-hand and
||| right-hand side of the pattern arrow "=>".
|||
||| This is an alias for `PatClause EmptyFC`.
public export %inline
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

||| A with clause.
|||
||| This is an alias for `WithClause EmptyFC`.
public export %inline
withClause :
     (lhs     : TTImp)
  -> (rig     : Count)
  -> (wval    : TTImp)
  -> (prf     : Maybe Name)
  -> (flags   : List WithFlag)
  -> (clauses : List Clause)
  -> Clause
withClause = WithClause EmptyFC

||| A case expression.
|||
||| This is an alias for `ICase EmptyFC []`.
public export %inline
iCase : (sc : TTImp) -> (ty : TTImp) -> (clauses : List Clause) -> TTImp
iCase = ICase EmptyFC []

||| "as"-pattern.
|||
||| This is an alias for `IAs EmptyFC UseLeft`.
public export %inline
as : Name -> TTImp -> TTImp
as = IAs EmptyFC EmptyFC UseLeft

--------------------------------------------------------------------------------
--          Function Declarations
--------------------------------------------------------------------------------

||| Named type.
|||
||| This is an alias for `MkTyp EmptyFC`.
public export %inline
mkTy : (name : Name) -> (type : TTImp) -> ITy
mkTy = MkTy EmptyFC . MkFCVal EmptyFC

||| Type declaration of a function.
|||
||| `claim c v opts n tp` is an alias for
||| `IClaim EmptyFC c v opts (MkTy EmptyFC n tp)`.
public export %inline
claim :
     (count : Count)
  -> (vis   : Visibility)
  -> (opts  : List FnOpt)
  -> (name  : Name)
  -> (type  : TTImp)
  -> Decl
claim c v opts n tp = IClaim $ MkFCVal EmptyFC $ MkIClaimData c v opts (mkTy n tp)

||| `simpleClaim v n t` is an alias for `claim MW v [] (mkTy n t)`
public export %inline
simpleClaim : Visibility -> Name -> TTImp -> Decl
simpleClaim v = claim MW v []

||| Alias for `simpleClaim Public`
public export %inline
public' : Name -> TTImp -> Decl
public' = simpleClaim Public

||| Alias for `simpleClaim Private``
public export %inline
private' : Name -> TTImp -> Decl
private' = simpleClaim Private

||| Alias for `simpleClaim Export`
public export %inline
export' : Name -> TTImp -> Decl
export' = simpleClaim Export

||| `directHint v` is an alias for `claim MW v [Hint True]`
public export %inline
directHint : Visibility -> Name -> TTImp -> Decl
directHint v = claim MW v [Hint True]

||| `interfaceHint v opts` is an alias for `claim MW v (Hint False :: opts)`
public export %inline
interfaceHintOpts : Visibility -> List FnOpt -> Name -> TTImp -> Decl
interfaceHintOpts v opts = claim MW v (Hint False :: opts)

||| `interfaceHint v` is an alias for `claim MW v [Hint False]`
public export %inline
interfaceHint : Visibility -> Name -> TTImp -> Decl
interfaceHint v = claim MW v [Hint False]

||| Function definition (implementation)
|||
||| This is an alias for `IDef EmptyFC`.
public export %inline
def : Name -> List Clause -> Decl
def = IDef EmptyFC

--------------------------------------------------------------------------------
--          Local Defs and Let
--------------------------------------------------------------------------------

||| Let bindings.
|||
||| This is an alias for `ILet EmptyFC`.
public export %inline
iLet :
     (count : Count)
  -> (name  : Name)
  -> (type  : TTImp)
  -> (val   : TTImp)
  -> (scope : TTImp)
  -> TTImp
iLet = ILet EmptyFC EmptyFC

||| Local definitions
|||
||| This is an alias for `ILocal EmptyFC`.
public export %inline
local : (decls : List Decl) -> (scope : TTImp) -> TTImp
local = ILocal EmptyFC

||| Field updates
|||
||| This is an alias for `IUpdate EmptyFC`.
public export %inline
update : (updates : List IFieldUpdate) -> (arg : TTImp) -> TTImp
update = IUpdate EmptyFC

--------------------------------------------------------------------------------
--          Data Declarations
--------------------------------------------------------------------------------

||| Data declaration.
|||
||| This merges constructors `IData` and `MkData`.
public export
iData :
     (vis   : Visibility)
  -> (name  : Name)
  -> (tycon : TTImp)
  -> (opts  : List DataOpt)
  -> (cons  : List ITy)
  -> Decl
iData v n tycon opts cons =
  IData EmptyFC (specified v) Nothing (MkData EmptyFC n (Just tycon) opts cons)

||| Simple data declaration of type `Type` (no options, no parameters,
||| no indices).
|||
||| `simpleData v n` is an alias for `iData v n type []`.
public export %inline
simpleData : Visibility -> Name -> (cons : List ITy) -> Decl
simpleData v n = iData v n type []

||| Alias for `simpleData Public`
public export %inline
simpleDataPublic : Name -> (cons : List ITy) -> Decl
simpleDataPublic = simpleData Public

||| Alias for `simpleData Export`
public export %inline
simpleDataExport : Name -> (cons : List ITy) -> Decl
simpleDataExport = simpleData Export

--------------------------------------------------------------------------------
--          Rewrite
--------------------------------------------------------------------------------

||| Alias for `IRewrite EmptyFC`
public export %inline
iRewrite : (eq,scope : TTImp) -> TTImp
iRewrite = IRewrite EmptyFC

--------------------------------------------------------------------------------
--          Laziness
--------------------------------------------------------------------------------

||| Alias for `IDelayed EmptyFC`
public export %inline
iDelayed : (reason : LazyReason) -> (arg : TTImp) -> TTImp
iDelayed = IDelayed EmptyFC

||| Alias for `IDelay EmptyFC`
public export %inline
iDelay : (arg : TTImp) -> TTImp
iDelay = IDelay EmptyFC

||| Alias for `IForce EmptyFC`
public export %inline
iForce : (arg : TTImp) -> TTImp
iForce = IForce EmptyFC

--------------------------------------------------------------------------------
--          Quotation
--------------------------------------------------------------------------------

||| Alias for `IQuote EmptyFC`
public export %inline
quote : TTImp -> TTImp
quote = IQuote EmptyFC

||| Alias for `IQuoteName EmptyFC`
public export %inline
quoteName : Name -> TTImp
quoteName = IQuoteName EmptyFC

||| Alias for `IQuoteDecl EmptyFC`
public export %inline
quoteDecl : List Decl -> TTImp
quoteDecl = IQuoteDecl EmptyFC

||| Alias for `IUnquote EmptyFC`
public export %inline
unquote : TTImp -> TTImp
unquote = IUnquote EmptyFC

--------------------------------------------------------------------------------
--          Recursion
--------------------------------------------------------------------------------


||| Checks if one of the given names makes an appearance in the
||| given type.
export
rec : List Name -> (tpe : TTImp) -> Bool
rec nms (IVar fc nm1)        = nm1 `elem` nms
rec nms (IApp fc s t)        = rec nms s || rec nms t
rec nms (INamedApp fc s _ t) = rec nms s || rec nms t
rec nms (IAutoApp fc s t)    = rec nms s || rec nms t
rec nms (IDelayed _ LLazy t) = rec nms t
rec nms t                    = False

||| Prefixes the given expression with `assert_total`, if
||| one of the names listed makes an appearance in the given type.
export
assertIfRec : List Name -> (tpe : TTImp) -> (expr : TTImp) -> TTImp
assertIfRec nms tpe expr =
  if rec nms tpe then var "assert_total" `app` expr else expr

--------------------------------------------------------------------------------
--          Elab Utils
--------------------------------------------------------------------------------

||| Constructs a `TTImp` from the given arguments, which
||| wraps them in unqualified list constructors.
|||
||| For instance, `listOf [var "x", var "y"]` generates
||| an expression corresponding to `x :: y :: Nil`
public export %inline
listOf : Foldable t => t TTImp -> TTImp
listOf = foldr (\e,acc => `(~(e) :: ~(acc))) `( Nil )

private errMsg : Name -> List (Name,TTImp) -> String
errMsg n [] = show n ++ " is not in scope."
errMsg n xs =
  let rest := concat $ intersperse ", " $ map (show . fst) xs
   in show n ++ " is not unique: " ++ rest

lookupRefinedName : Elaboration m => (prev : List (Name, TTImp)) -> Name -> m (Name, TTImp)
lookupRefinedName prev n = case !(getType n) of
  [p] => pure p
  []  => fail $ errMsg n prev
  ps  => fail $ errMsg n ps

||| Looks up a name in the current namespace.
export
lookupName : Elaboration m => Name -> m (Name, TTImp)
lookupName n = do
  pairs <- getType n
  case pairs of
    [p] => pure p
    ps  => case n of
             UN _ => inCurrentNS n >>= lookupRefinedName ps
             _    => fail $ errMsg n ps
