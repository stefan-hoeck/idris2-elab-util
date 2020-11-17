# idris2-elab-util

Utilities and documentation for exploring Idris 2 elaborator reflection.
For a tutorial-ish introduction, [start here](/src/Doc/Meta.md).

Part of the utilities in this package as well as some of my understanding
of elaborator reflection in Idris came from
the [idris2-elab-deriving](https://github.com/MarcelineVQ/idris2-elab-deriving)
package.

## Docs and Tutorial

Most tutorials in this repository are themselves literate Idris files.
In order to typecheck or build those, package file elab-util-docs.ipkg
is provided.

## Related Libraries

Part of the utilities in this package are put to work in
[idris2-sop](https://github.com/stefan-hoeck/idris2-sop)
a (still very experimental and incomplete) port of Haskell's
[sop-core](https://hackage.haskell.org/package/sop-core) and
[generic-sop](https://hackage.haskell.org/package/generics-sop)
packages useful to automatically derive interface implementations.
