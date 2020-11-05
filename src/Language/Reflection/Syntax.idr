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
import Language.Reflection.Pretty

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

||| Takes a (probably fully qualified name) and generates a
||| identifier from this without the dots.
|||
||| Example : camelCase "Data.List1.List1" = "DataList1List1"
export
camelCase : Name -> String
camelCase = concat . split ('.' ==) . show

--------------------------------------------------------------------------------
--          Vars
--------------------------------------------------------------------------------

||| Creates a variable from the given name
|||
||| Names are best created using quotes: `{{ AName }},
||| `{{ In.Namespacs.Name }}.
|||
||| Likewise, if the name is already known at the time of
||| writing, use quotes for defining variables directly: `(AName)
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
--          Function Arguments
--------------------------------------------------------------------------------

public export
record Arg where
  constructor MkArg
  count   : Count
  piInfo  : PiInfo TTImp
  name    : Maybe Name
  type    : TTImp

export
arg : TTImp -> Arg
arg = MkArg MW ExplicitArg Nothing

export
isExplicit : Arg -> Bool
isExplicit (MkArg _ ExplicitArg _ _) = True
isExplicit (MkArg _ _           _ _) = False

export
Pretty Arg where
  pretty (MkArg count piInfo name type) =
    parens $ hsepH [count, piInfo, name, ":", type]

||| Extracts the arguments from a function type.
export
unPi : TTImp -> (List Arg, TTImp)
unPi (IPi _ c p n at rt) = let (args,rt') = unPi rt
                            in (MkArg c p n at :: args, rt')
unPi tpe                 = ([],tpe)

||| Extracts the arguments from a function type.
export
unLambda : TTImp -> (List Arg, TTImp)
unLambda (ILam _ c p n at rt) = let (args,rt') = unLambda rt
                                 in (MkArg c p n at :: args, rt')
unLambda tpe                  = ([],tpe)

export
zipWithIndex : List a -> List (Int,a)
zipWithIndex = run 0
  where run : Int -> List a -> List (Int,a)
        run _ []       = []
        run n (h :: t) = (n,h) :: run (n + 1) t

||| Creates argument names `["x0","x1",...]`
||| for the arguments of a constructor.
export
argNames : List a -> List String
argNames = map (\(n,_) => "x" ++ show n) . zipWithIndex

--------------------------------------------------------------------------------
--          Lambdas
--------------------------------------------------------------------------------

||| Defines an anonymous function (lambda).
|||
||| This passes the fields of `Arg` to `ILam EmptyFC`
export
lam : Arg -> (lamTy : TTImp) -> TTImp
lam (MkArg c p n t) = ILam EmptyFC c p n t

infixr 3 .=>

||| Infix alias for `lam`.
export
(.=>) : Arg -> TTImp -> TTImp
(.=>) = lam

--------------------------------------------------------------------------------
--          Function Types
--------------------------------------------------------------------------------

||| Defines a function type.
|||
||| This passes the fields of `Arg` to `IPi EmptyFC`
export
pi : Arg -> (retTy : TTImp) -> TTImp
pi (MkArg c p n t) = IPi EmptyFC c p n t

infixr 5 .->

||| Infix alias for `pi`.
export
(.->) : Arg -> TTImp -> TTImp
(.->) = pi

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

infixr 3 .=

||| Infix alias for `patClause`
export
(.=) : TTImp -> TTImp -> Clause
(.=) = patClause

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
||| `claim c v opts n tp` is an alias for
||| `IClaim EmptyFC c v opts (MkTy EmptyFC n tp)`.
export
claim : Count -> Visibility -> List FnOpt -> Name -> TTImp -> Decl
claim c v opts n tp = IClaim EmptyFC c v opts (mkTy n tp)

||| `simpleClaim v n t` is an alias for `claim MW v [] (mkTy n t)`
export
simpleClaim : Visibility -> Name -> TTImp -> Decl
simpleClaim v = claim MW v []

||| Alias for `simpleClaim Public`
export
public' : Name -> TTImp -> Decl
public' = simpleClaim Public

||| Alias for `simpleClaim Private``
export
private' : Name -> TTImp -> Decl
private' = simpleClaim Private

||| Alias for `simpleClaim Export`
export
export' : Name -> TTImp -> Decl
export' = simpleClaim Export

||| `directHint v` is an alias for `claim MW v [Hint True]`
export
directHint : Visibility -> Name -> TTImp -> Decl
directHint v = claim MW v [Hint True]

||| `interfaceHint v` is an alias for `claim MW v [Hint False]`
export
interfaceHint : Visibility -> Name -> TTImp -> Decl
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

||| Looks up a name in the current namespace.
export
lookupName : Name -> Elab (Name, TTImp)
lookupName n = do pairs <- getType n 
                  case (pairs,n) of
                       ([p],_)     => pure p
                       (ps,UN str) => inCurrentNS (UN str) >>= lookupName
                       (ps,_)      => fail $ errMsg n ps
