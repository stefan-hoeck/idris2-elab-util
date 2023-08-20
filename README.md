# Idris 2 Elaborator Reflection : Utilities and Documentation

Utilities and documentation for exploring Idris 2 elaborator reflection.
For a tutorial-ish introduction, [start here](/src/Doc/Index.md).

Part of the utilities in this package as well as some of my understanding
of elaborator reflection in Idris came from
the [idris2-elab-deriving](https://github.com/MarcelineVQ/idris2-elab-deriving)
package.

## Docs and Tutorial

Most tutorial pages in this repository are themselves literate Idris files.
In order to typecheck or build those, package file elab-util-docs.ipkg
is provided.

## Related Libraries

Part of the utilities in this package are put to work in
[idris2-sop](https://github.com/stefan-hoeck/idris2-sop)
a (still very experimental and incomplete) port of Haskell's
[sop-core](https://hackage.haskell.org/package/sop-core) and
[generic-sop](https://hackage.haskell.org/package/generics-sop)
packages useful to automatically derive interface implementations.

## Supported Idris Versions
Starting from Idris2 version 0.5.1, tagged releases of the same
minor version number (e.g. 0.5.x) will be made available, while the main
branch keeps following the Idris2 main branch

Since Idris2 releases are happening rather infrequently at the moment,
it is suggested to use
a package manager like [pack](https://github.com/stefan-hoeck/idris2-pack)
to install and maintain matching versions of the Idris compiler
and this library.

## Contributors

Contributions are highly welcome. Please adhere to the
[style guide](https://github.com/stefan-hoeck/idris2-style-guide)
I use for my projects.
