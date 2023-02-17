||| When different modules export an operator with different
||| fixity/associativity annotations, the last one imported wins. This
||| behaviour may introduce unexpected errors if an
||| indirectly-imported module's fixity clashes.
|||
||| If you get an error about the operators (.=>), import this module
module Language.Reflection.BugFixity

infixr 3 .=>
