||| Utility types and functions for automatically deriving
||| interface instances. So far, this module does not provide
||| deriving functions for existing interfaces. See
||| Doc.Generic4 for examples, how this could be done
||| using the functionality provided here.
module Language.Reflection.Derive

import public Language.Reflection.Syntax
import public Language.Reflection.Types

||| Utility type for deriving interface implementations
||| automatically. See implementations of `Eq'` and `Ord'`
||| in Doc.Generic4 as examples, how this can be done.
public export
record DeriveUtil where
  constructor MkDeriveUtil

  ||| The underlying type info containing the list and names
  ||| of data constructors plus their arguments as well as
  ||| the data type's name and type arguments.
  typeInfo           : ParamTypeInfo

  ||| Fully applied data type, i.e. `var "Either" .$ var "a" .$ var "b"`
  appliedType        : TTImp 

  ||| The names of type parameters
  paramNames         : List Name

  ||| Types of constructor arguments where at least one
  ||| type parameter makes an appearance. These are the
  ||| `tpe` fields of `ExplicitArg` where `hasParam`
  ||| is set to true. See the documentation of `ExplicitArg`
  ||| when this is the case
  argTypesWithParams : List TTImp


||| Creates a deriving utility from information about
||| a (possibly) parameterized type.
export
genericUtil : ParamTypeInfo -> DeriveUtil
genericUtil ti = let pNames = map fst $ params ti
                     appTpe = appNames (name ti) pNames
                     twps   = concatMap hasParamTypes ti.cons
                  in MkDeriveUtil ti appTpe pNames twps

||| Generates the name of an interface's implementation function
export
implName : DeriveUtil -> String -> Name
implName g interfaceName =  UN $ "impl" ++ interfaceName
                                        ++ nameStr g.typeInfo.name

||| Syntax tree and additional info about the
||| implementation function of an interface.
|||
||| With 'implementation function', we mean the following:
||| When deriving an interface implementation, the elaborator
||| creates a function returning the corresponding record value.
||| Values of this record should provide both the full type
||| and implementation of this function as `TTImp` values.
|||
||| ```idris exampel
||| public export
||| implEqEither : {0 a : _} -> {0 b : _} -> Eq a => Eq b => Eq (Either a b)
||| implEqEither = ?impl
||| ```
public export
record InterfaceImpl where
  constructor MkInterfaceImpl
  ||| The interface's name, for instance "Eq" ord "Ord".
  ||| This is used to generate the name of the
  ||| implementation function.
  interfaceName : String

  ||| Visibility of the implementation function.
  visibility    : Visibility

  ||| Actual implementation of the implementation function.
  ||| This will be the right hand side of the sole pattern clause
  ||| in the function definition.
  |||
  ||| As an example, assume there is a `genEq` function used
  ||| as an implementation for `(==)` for data types with
  ||| some kind of `Generic` instance (see the tutorial on
  ||| Generics for more information about this). An implementation
  ||| for interface `Eq` could then look like this:
  |||
  ||| ```idirs example
  ||| impl = var (singleCon "Eq") .$ `(genEq) .$ `(\a,b => not (a == b))
  ||| ```
  impl          : TTImp

  ||| Full type of the implementation function, including
  ||| implicit arguments (type parameters), which have to be part
  ||| of the `TTImp`.
  |||
  ||| See also `implementationType`, a utility function to create this
  ||| kind of function types for type classes with a single parameter
  ||| of type `Type`.
  |||
  ||| Example:
  |||
  ||| ```idirs example
  ||| `({0 a: _} -> {0 b : _} -> Eq a => Eq b => Eq (Either a b))
  ||| ```
  type          : TTImp

private
implDecl : DeriveUtil -> (DeriveUtil -> InterfaceImpl) -> List Decl
implDecl g f = let (MkInterfaceImpl iname vis impl type) = f g
                   function = implName g iname

                in [ interfaceHint vis function type
                   , def function [var function .= impl] ]

private
deriveDecls : Name -> List (DeriveUtil -> InterfaceImpl) -> Elab (List Decl)
deriveDecls name fs = mkDecls <$> getParamInfo' name 
  where mkDecls : ParamTypeInfo -> List Decl
        mkDecls pi = let g = genericUtil pi
                      in concatMap (implDecl g) fs
                  
||| Given a name of a data type plus a list of interfaces, tries
||| to implement these interfaces automatically using
||| elaborator reflection.
|||
||| Again, see Doc.Generic4 for a tutorial and examples how
||| to use this.
export
derive : Name -> List (DeriveUtil -> InterfaceImpl) -> Elab ()
derive name fs = do decls <- deriveDecls name fs
                    declare decls

||| Given a `TTImp` representing an interface, generates
||| the type of the implementation function with all type
||| parameters applied and auto implicits specified.
|||
||| Example: Given the `DeriveUtil` info of `Either`, this
||| will generate the following type for input ``(Eq)`:
|||
||| ```idris example
||| {0 a : _} -> {0 b : _} -> Eq a => Eq b => Eq (Either a b)
||| ```
|||
||| Note: This function is only to be used with single-parameter
||| type classes, whose type parameters are of type `Type`.
export
implementationType : (iface : TTImp) -> DeriveUtil -> TTImp
implementationType iface (MkDeriveUtil _ appTp names argTypesWithParams) =
  let appIface = iface .$ appTp
      autoArgs = piAllAuto appIface $ map (iface .$) argTypesWithParams
   in piAllImplicit autoArgs names
