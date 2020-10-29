## Introduction: Metaprogramming

Metaprogramming is about writing programs that write programs
typically by using existing programs as their input.
It is useful for instance to automate otherwise tedious tasks
by inspecting the structure of existing data or function definitions
and deriving new functions or data types from that structure.

In Idris2, metaprogramming consists of the following
three aspekts:

  * Inspecting the structure of existing definitions
  * Programmatically write new definitions
  * Include generated definitions in a project's source code

All of the above are provided though the base module `Language.Reflection`,
and in this tutorial we are going to look at each of them.

### TTImp: The Structure of Idris Programs

Modules `Language.Reflection.TT` and `Language.Reflection.TTImp` define
several data types used as intermediate representations of Idris2
programs during compilation. We will learn how to use these
representations both to inspect existing definitions and
to programmatically generate new ones.

This library provides pretty printers for visualizing the structure
of `TTImp` values and utility functions for defining and
dissecting them.

### Quotes: Generating TTImp values from expressions

Writing `TTImp` trees manually can be verbouse, tedious and error-prone.
Idris provides several types of quotes to convert valid
expressions directly to the corresponding tree structures.
This is useful both to define the static parts of a metaprogram
and to inspect the syntax trees of expressions we'd like
to define or dissect programmatically.

### Elab: A Monad for Metaprogramming

Module `Language.Reflection` defines `Elab`, an abstract monadic
data type used to manipulate programs at compile time. The
module provides functionality for looking up existing
data definitions in scope as well as add new declarations
to the list of declarations in a source file.

### What's next

This was a rather superficial introduction to the core
concepts of metaprogramming in Idris. It is now time
to get our hands dirty and learn how to
[inspect the structure of Idris programs](Inspect.md).
