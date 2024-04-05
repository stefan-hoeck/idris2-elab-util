||| Operator aliases for some of the functions in
||| `Language.Reflection.Syntax`.
|||
||| There are placed in a separate module in order not to
||| pollute the envirionment with additional fixity declarations.
module Language.Reflection.Syntax.Ops

import Language.Reflection
import Language.Reflection.Syntax

%default total

export infixl 6 .$,.@,.!

||| Infix version of `app`
|||
||| Example: ```var "Just" .$ var "x"```
public export %inline
(.$) : TTImp -> TTImp -> TTImp
(.$) = IApp EmptyFC

||| Infix version of `namedApp`.
public export %inline
(.!) : TTImp -> (Name,TTImp) -> TTImp
s .! (n,t) = namedApp s n t

-- Use same fixity as in `Syntax.PreorderReasoning.Generic`
export infix 1 .=>

||| Infix alias for `lam`.
|||
||| @deprecation: This is in conflict with a similar operator from
||| `Syntax.PreorderReasoning`. It will be removed in a later commit.
public export %inline %deprecate
(.=>) : Arg -> TTImp -> TTImp
(.=>) = lam

export infixr 5 .->

||| Infix alias for `pi`.
public export %inline
(.->) : Arg -> TTImp -> TTImp
(.->) = pi

export infixr 3 .=

||| Infix alias for `patClause`
public export %inline
(.=) : TTImp -> TTImp -> Clause
(.=) = patClause
