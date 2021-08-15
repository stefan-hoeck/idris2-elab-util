export IDRIS2 ?= idris2

lib_pkg = elab-util.ipkg

docs_pkg = elab-util-docs.ipkg

.PHONY: all lib doc install clean clean-install repl develop

all: lib docs

clean-install: clean install

lib:
	${IDRIS2} --build ${lib_pkg}

docs:
	${IDRIS2} --build ${docs_pkg}

install:
	${IDRIS2} --install ${lib_pkg}

clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${docs_pkg}
	${RM} -r build

# Start a REPL in rlwrap
repl:
	rlwrap -pGreen ${IDRIS2} --find-ipkg src/Language/Reflection/Pretty.idr

develop:
	find -name "*.idr" | entr -d idris2 --typecheck ${lib_pkg}
