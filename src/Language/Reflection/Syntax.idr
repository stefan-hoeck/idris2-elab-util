||| Some utilities for defining and manipulating TTImp values
||| for writing elaborator scripts.
|||
||| Some notes: Use quotes whenever possible:
|||
||| Names can be quoted like so: `{{ AName }}, `{{ In.Namespace.AName }}.
||| Both examples are of type Language.Reflection.TT.Name.
|||
||| Expressions can be quoted like so: `(\x => x * x)
module Language.Reflection.Syntax

import public Data.Strings
import public Data.List1
import public Language.Reflection

--------------------------------------------------------------------------------
--          Names
--------------------------------------------------------------------------------

public export
FromString Name where
  fromString s = run (split ('.' ==) s) []
    where run : List1 String -> List String -> Name
          run (h ::: []) []        = UN h
          run (h ::: []) ns        = NS (MkNS ns) (UN h)
          run (h ::: (y :: ys)) xs = run (y ::: ys) (h :: xs)

--------------------------------------------------------------------------------
--          Vars
--------------------------------------------------------------------------------

||| Creates a variable from the given name
|||
||| Names are best created using name quotes: `{{ AName }},
||| `{{ In.Namespacs.Name }}.
|||
||| Likewise, if the name is already known at the time of
||| writing, use quotes for defining a variable directly: `(AName)
export
var : Name -> TTImp
var = IVar EmptyFC

||| Alias for `var . fromString`
export
varStr : String -> TTImp
varStr = var . fromString

||| Binds a new variable, for instance in a pattern match.
|||
||| This is an alias for `IBindVar EmptyFC`.
export
bindVar : String -> TTImp
bindVar = IBindVar EmptyFC

||| Implicit value bound if unsolved
|||
||| This is an alias for `Implicit EmptyFC True`
export
implicitTrue : TTImp
implicitTrue = Implicit EmptyFC True

||| Implicitly typed value unbound if unsolved
|||
||| This is an alias for `Implicit EmptyFC False`
export
implicitFalse : TTImp
implicitFalse = Implicit EmptyFC False

||| Primitive values.
|||
||| This is an alias for `IPrimVal EmptyFC`
export
primVal : (c : Constant) -> TTImp
primVal = IPrimVal EmptyFC


||| The type `Type`.
|||
||| This is an alias for `IType EmptyFC`.
export
type :  TTImp
type = IType EmptyFC

--------------------------------------------------------------------------------
--          Application
--------------------------------------------------------------------------------

||| Function application.
|||
||| This is an alias for `IApp EmptyFC`.
|||
||| Example: ```app (var "Just") (var "x")```
|||          is equivalent to `(Just x)
export
app : TTImp -> TTImp -> TTImp
app = IApp EmptyFC

infixl 6 .$

||| Infix version of `app`
|||
||| Example: ```var "Just" .$ var "x"```
export
(.$) : TTImp -> TTImp -> TTImp
(.$) = IApp EmptyFC

appNames : (f : a -> TTImp) -> Name -> List a -> TTImp
appNames f fun = run (var fun)
  where run : TTImp -> List a -> TTImp
        run tti []        = tti
        run tti (x :: xs) = run (tti .$ f x) xs

||| Applies a list of variables to a function.
|||
||| Example: appAll "either" ["f","g","val"]
|||          is equivalent to ~(either f g val)
export
appAll : (fun : Name) -> (args : List Name) -> TTImp
appAll = appNames var

||| Binds a list of parameters to a data constructor in
||| a pattern match.
|||
||| Example: bindAll "MkPair" ["a","b"]
|||          is the same as ~(MkPair a b)
export
bindAll : (fun : Name) -> (args : List String) -> TTImp
bindAll = appNames bindVar

export
implicitApp : TTImp -> Maybe Name -> TTImp -> TTImp
implicitApp = IImplicitApp EmptyFC

--------------------------------------------------------------------------------
--          Lambdas
--------------------------------------------------------------------------------

||| Defines an anonymous function (lambda).
|||
||| This is an alias for `ILam EmptyFC`.
export
lam : Count -> PiInfo TTImp -> Maybe Name ->
      (argTy : TTImp) -> (lamTy : TTImp) -> TTImp
lam = ILam EmptyFC

infixr 3 .=>

||| Infix alias for `lam MW ExplicitArg Nothing`.
export
(.=>) : TTImp -> TTImp -> TTImp
(.=>) = lam MW ExplicitArg Nothing

--------------------------------------------------------------------------------
--          Function Types
--------------------------------------------------------------------------------

||| Defines a function type.
|||
||| This is an alias for `IPi EmptyFC`.
export
pi : Count -> PiInfo TTImp -> Maybe Name ->
     (argTy : TTImp) -> (retTy : TTImp) -> TTImp
pi = IPi EmptyFC

infixr 3 .->

||| Infix alias for `pi MW ExplicitArg Nothing`.
export
(.->) : TTImp -> TTImp -> TTImp
(.->) = pi MW ExplicitArg Nothing

--------------------------------------------------------------------------------
--          Pattern Matching
--------------------------------------------------------------------------------

||| A pattern clause consisting of the left-hand and
||| right-hand side of the pattern arrow "=>".
|||
||| This is an alias for `PatClause EmptyFC`.
export
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC

||| A case expression.
|||
||| This is an alias for `ICase EmptyFC`.
export
iCase : TTImp -> (ty : TTImp) -> List Clause -> TTImp
iCase = ICase EmptyFC

||| "as"-pattern.
|||
||| This is an alias for `IAs EmptyFC UseLeft`.
export
as : Name -> TTImp -> TTImp
as = IAs EmptyFC UseLeft  

--------------------------------------------------------------------------------
--          Function Declarations
--------------------------------------------------------------------------------

||| Named type.
|||
||| This is an alias for `MkTyp EmptyFC`.
export
mkTy : (n : Name) -> (ty : TTImp) -> ITy
mkTy = MkTy EmptyFC

||| Type declaration of a function.
|||
||| This is an alias for `IClaim EmptyFC`.
export
claim : Count -> Visibility -> List FnOpt -> ITy -> Decl
claim = IClaim EmptyFC

||| `simpleClaim v` is an alias for `claim MW v []`
export
simpleClaim : Visibility -> ITy -> Decl
simpleClaim v = claim MW v []

||| `directHint v` is an alias for `claim MW v [Hint True]`
export
directHint : Visibility -> ITy -> Decl
directHint v = claim MW v [Hint True]

||| `interfaceHint v` is an alias for `claim MW v [Hint False]`
export
interfaceHint : Visibility -> ITy -> Decl
interfaceHint v = claim MW v [Hint False]

||| Function definition (implementation)
|||
||| This is an alias for `IDef EmptyFC`.
export
def : Name -> List Clause -> Decl
def = IDef EmptyFC

||| Local definitions
|||
||| This is an alias for `ILocal EmptyFC`.
export
local : List Decl -> TTImp -> TTImp
local = ILocal EmptyFC

--------------------------------------------------------------------------------
--          Data Declarations
--------------------------------------------------------------------------------

||| Data declaration.
|||
||| This merges constructors `IData` and `MkData`.
export
iData :  Visibility
      -> Name
      -> (tycon : TTImp)
      -> (opts  : List DataOpt)
      -> (cons  : List ITy)
      -> Decl
iData v n tycon opts cons = IData EmptyFC v (MkData EmptyFC n tycon opts cons)

||| Simple data declaration of type `Type` (no options, no parameters,
||| no indices).
|||
||| `simpleData v n` is an alias for `iData v n type []`.
export
simpleData : Visibility -> Name -> (cons : List ITy) -> Decl
simpleData v n = iData v n type []

||| Alias for `simpleData Public`
export
simpleDataPublic : Name -> (cons : List ITy) -> Decl
simpleDataPublic = simpleData Public

||| Alias for `simpleData Export`
export
simpleDataExport : Name -> (cons : List ITy) -> Decl
simpleDataExport = simpleData Export

--------------------------------------------------------------------------------
--          Local Definitions
--------------------------------------------------------------------------------

||| Let bindings.
|||
||| This is an alias for `ILet EmptyFC`.
export
iLet : Count -> Name -> (nTy : TTImp) -> (nVal : TTImp)
    -> (scope : TTImp) -> TTImp
iLet = ILet EmptyFC

--------------------------------------------------------------------------------
--          Elab Utils
--------------------------------------------------------------------------------

export
listOf : List TTImp -> TTImp
listOf [] = `( Nil )
listOf (x :: xs) = `( ~(x) :: ~(listOf xs) )

private errMsg : Name -> List (Name,TTImp) -> String
errMsg n [] = show n ++ " is not in scope."
errMsg n xs = let rest = concat $ intersperse ", " $ map (show . fst) xs
               in show n ++ " is not unique: " ++ rest

export
adjustNS : Name -> Elab Name
adjustNS n@(UN _) = inCurrentNS n
adjustNS n        = pure n

||| Looks up a name in the current namespace.
export
lookupName : Name -> Elab (Name, TTImp)
lookupName n' = do
  n            <- adjustNS n'
  [(name,imp)] <- getType n | xs => fail $ errMsg n' xs
  pure (name,imp)

export
getExplicitArgs : Name -> Elab (List Name)
getExplicitArgs n = lookupName n >>= (run . snd)
  where
    run : TTImp -> Elab (List Name)
    run (IPi _ _ ExplicitArg _ _ retTy) = [| genSym "arg" :: run retTy |]
    run (IPi _ _ _ _ _ retTy)           = run retTy -- skip implicit args
    run _                               = pure []

export
printLocalVars : Elab ()
printLocalVars = do vs <- localVars
                    logMsg "Local vars: " 10 (show vs)
