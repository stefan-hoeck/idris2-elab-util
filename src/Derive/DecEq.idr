module Derive.DecEq

import Language.Reflection.Util 
import Decidable.Equality
import Language.Reflection.Pretty
import Language.Reflection.Syntax
import Language.Reflection.Syntax.Ops
import Language.Reflection
import Data.Vect
import Data.DPair
import Data.List1
import Data.SortedMap as M
import Data.List.Quantifiers

%default total

appToName : String -> Name -> Name 
appToName s (NS ns n) = NS ns (appToName s n)
appToName s (UN (Basic str)) = UN (Basic (str ++ s))
appToName s (UN (Field str)) = UN (Field (str ++ s))
appToName s (UN Underscore) = UN Underscore --todo 
appToName s (MN str i) = MN (str ++ s) i
appToName s (DN str i) = DN (str ++ s) i
appToName s (Nested i nm) = Nested i (appToName s nm)
appToName s (CaseBlock str i) = CaseBlock (str ++ s) i
appToName s (WithBlock str i) = WithBlock (str ++ s) i 

mkArg : PiInfo TTImp -> Maybe Name -> TTImp -> Arg 
mkArg = MkArg MW

mkUN : String -> Name 
mkUN x = UN $ Basic x

mkUNMaybe : Maybe Name -> Name 
mkUNMaybe (Just s) = s
mkUNMaybe Nothing = UN Underscore

deriveDecEqDef: TypeInfo -> List Nat -> List (String, String) -> Elab (List Clause) 
deriveDecEqDef ti parampos casesStr = let
    -- constructor pairs from string pairs returned from elab call  
    strsToCons : List (String, String) -> Elab (List (Con ti.arty ti.args, Con ti.arty ti.args))
    strsToCons [] = pure []
    strsToCons ((x, y) :: xs) = let 
        findf : String -> Con n vs -> Bool
        findf x e = let 
            xname : Name = fromString x
            ename : Name = e.getName
            in 
                xname == ename || dropNS xname == dropNS ename 
        in case (find (findf x) ti.cons, 
                  find (findf y) ti.cons) of
            (Just x', Just y') => (::) <$> pure (x', y') <*> (strsToCons xs)
            (_, _) =>  fail $ "strToCons: no constructor found"
    -- for some constructor, the names of all explicit args and whether they are to be split on or not
    splitCons : {vs : Vect n Arg} -> Con n vs -> Elab (q ** Vect q (Name, Bool))
    splitCons {vs = vs} c = let 
        idxdArgs : Vect c.arty (Arg, Nat) = zip {z = Vect c.arty} c.args (map finToNat Fin.range)
        splitInfoIdxdArgs : Vect c.arty (Arg, Bool) = map (\(a, i) => (a, not (elem i parampos))) idxdArgs
        (p ** args) = Data.Vect.filter (\(MkArg _ i _ _, _) => i == ExplicitArg) splitInfoIdxdArgs
        fr : Vect p Name = freshNames (nameStr c.name) p
        v' : Vect p (Name, Bool) = zip {z=Vect p} fr (map Builtin.snd args)
        in pure (p ** v')
    
    -- makes a list of arguments for the constructor passed in. if the term needs to be split on, appends i to the variable for the term.
    mkArgs :  Maybe String -> Con ti.arty ti.args -> Elab (Name, (q ** Vect q Name))
    mkArgs i c = do 
        (p ** cons) <- splitCons c
        names : Vect p Name <- traverse (\(n, b) => pure $ if b then (appToName (fromMaybe "" i) n) else n) cons
        pure $ (c.name, (p ** names))

    -- make a ttimp from a constructor and its arguments 
    mkConTm : (Name, (q ** Vect q Name)) -> TTImp
    mkConTm (i, (_ ** cs)) = foldl (.$) (var i) (map bindVar cs) 

    -- case for unequal constructors
    unEqCons : TTImp
    unEqCons = var "No" .$ (lam (mkArg ExplicitArg (Just "h") implicitFalse)
                (iCase
                    { sc = var "h"
                    , ty = implicitFalse
                    , clauses = [ImpossibleClause EmptyFC (var "Refl")]
                    }))

    appNames : Name -> List Name -> TTImp
    appNames n xs = foldl (.$) (var n) (map bindVar xs)

    --  pass in the name of the constructor, the variables that have been resolved to equals for both terms, and the rest of the variables that need to be resolved
    --        conName dontSplit    withApp func              c1             c2
    mkWiths : Name -> List Name -> Maybe (TTImp -> TTImp) -> Vect p Name -> Vect p Name -> Elab Clause
    mkWiths cname cs Nothing Nil Nil = pure $ patClause {
        lhs = var "decEq" .$ appNames cname cs .$ appNames cname cs,
        rhs = var "Yes" .$ var "Refl"
    }
    mkWiths cname cs (Just wAppf) Nil Nil = pure $ patClause {
        lhs = wAppf ((var "decEq") .$ appNames cname cs .$ appNames cname cs),
        rhs = var "Yes" .$ var "Refl"
    }
    mkWiths cname cs wArgf xv@(x :: xs) yv@(y :: ys) = case x == y of 
        -- if the first argument does not need to be split on, add it to the list of precursor arguments and proceed
        True => mkWiths cname (cs ++ [x]) wArgf xs ys
        -- if the first argument does need to be split on
        False => do
            -- make argument terms for pattern match
            let xtm = appNames cname (cs ++ toList xv)
            let ytm = appNames cname (cs ++ toList yv)
            -- make applied terms for yes and no cases
            let yesTm = var "decEq" .$ (appNames cname (cs ++ [x] ++ toList xs)) .$ (appNames cname (cs ++ [x] ++ toList ys))
            let noTm = var "decEq" .$ xtm .$ ytm 
            -- for the yes case, add first argument to precursors (as they are assumed to be equal), and update with wArg function to add one more layer
            yesClause <- mkWiths cname (cs ++ [x]) (Just (\x => withApp {
                fun = (fromMaybe id wArgf) x, 
                arg = var "Yes" .$ var "Refl"})) xs ys
            let noClause = patClause {
                lhs = withApp {
                    fun = fromMaybe id wArgf $ noTm,
                    arg = var "No" .$ bindVar "prf"
                },
                rhs = var "No" .$ (lam (mkArg ExplicitArg (Just "h") implicitFalse) (var "prf" .$ iCase {
                    sc = var "h",
                    ty = implicitFalse, 
                    clauses = [var "Refl" .= var "Refl"]
                }))
            }
            pure $ withClause {
                lhs = fromMaybe id wArgf $ noTm, 
                rig = MW, 
                wval = var "Decidable.Equality.decEq" .$ var x .$ var y,
                prf = Nothing, 
                flags = [], 
                clauses = [yesClause, noClause]
            }

    -- makes the clause for a specific pair of constructors 
    mkCase : (Con ti.arty ti.args, Con ti.arty ti.args) -> Elab Clause
    mkCase (c1, c2) = do
            c1'@(n1, (p ** args1)) <- mkArgs (Just "1") c1
            c2'@(n2, (q ** args2)) <- mkArgs (Just "2") c2
            case (n1 == n2) of 
                False => pure $ patClause (var "decEq" .$ mkConTm c1' .$ mkConTm c2') unEqCons
                True => case (decEq p q) of 
                    No _ => fail "same constructor, different # args (should not happen)"
                    Yes prf => mkWiths n1 [] Nothing (replace {p=(\x => Vect x Name)} prf args1) args2 
    in do 
        cases <- strsToCons casesStr
        traverse mkCase cases

-- returns a list of inner DecEq constraints as autoimplicit args; 
-- for type constructor arguments that are types
getConstraints : List Arg -> List Arg
getConstraints [] = []
getConstraints (MkArg _ _ n (IType _) :: xs) = mkArg AutoImplicit Nothing (var "DecEq" .$ ((var . mkUNMaybe) n)) :: getConstraints xs 
getConstraints (MkArg _ _ n p@(IPi _ _ _ _ _ _) :: xs) = let 
    (piargs, ty) : (List Arg, TTImp) = unPi p 
    finalApp = IApp EmptyFC (var "DecEq") (foldl (.$) ((var . mkUNMaybe) n) 
                 (map (var . mkUNMaybe . .name) piargs))
    constr = mkArg AutoImplicit Nothing (foldr (.->) finalApp piargs)
    in constr :: getConstraints xs
getConstraints (_ :: xs) = getConstraints xs 

-- returns (claim for hint, claim for function)
deriveDecEqClaim : TypeInfo -> (TTImp, TTImp) 
deriveDecEqClaim ti = let 
    implicits = toList $ map (\(MkArg x _ n ty) => MkArg x ImplicitArg n ty)
                  ti.args
    qualTy = foldl (.$) (var ti.name) (map var ti.argNames)
    finalHint = var "DecEq" .$ qualTy
    constraints = getConstraints (toList ti.args)
    args = implicits ++ constraints
    claimHintTy = foldr (.->) finalHint args
    explicits = [mkArg ExplicitArg (Just (mkUN "t_x1")) qualTy
        , mkArg ExplicitArg (Just (mkUN "t_x2")) qualTy]
    finalFunc = var "Dec" .$ (var "===" .$ bindVar "t_x1" .$ bindVar "t_x2")
    claimFuncTy = foldr (.->) finalFunc (args ++ explicits)
    in
        (claimHintTy, claimFuncTy)

public export
deriveDecEq : a -> Elab ()
deriveDecEq a = do 
    IVar _ n <- quote a
        | _ => fail "not a variable"
    ti <- Language.Reflection.Types.getInfo' n
    (parampos, pairs) <- getDecEqConPairs a
    defn <- deriveDecEqDef ti parampos pairs
    let (clHint, clFunc) = deriveDecEqClaim ti
    let fName = UN . Basic $ "implDecEq" ++ (nameStr ti.name)
    let impl = local [private' (UN $ Basic "decEq") $ clFunc, 
                 def (UN $ Basic "decEq") defn] 
                  (var "__mkDecEq" .$ type (arg (varStr "decEq")))
    declare [interfaceHint Public fName clHint, def fName [var fName .= impl]]

-- to use, %runElab deriveDecEq <Type>
-- example: %runElab deriveDecEq Vect
-- to check if it worked, :doc Vect should show a hint for DecEq