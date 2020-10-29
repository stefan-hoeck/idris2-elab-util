## A First Metaprogram: Defining Enumerations

This tutorial is set up as a literate Idris file. We
therefore need some module noise to get started.

```idris
module Doc.Enum1

import Language.Reflection

%language ElabReflection
```

We often define sum types like `Weekday` below to define
a well-typed choice of concrete values.

```idris
public export
data Weekday = Monday
             | Tuesday
             | Wednesday
             | Thursday
             | Friday
             | Saturday
             | Sunday
```
