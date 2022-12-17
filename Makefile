export IDRIS2 ?= idris2

lib_pkg = elab-util.ipkg

docs_pkg = elab-util-docs.ipkg

test_pkg = elab-util-test.ipkg

PRETTIER_VERSION = 0.0.0

PRETTIER_RELATIVE_DIR = prettier-${PRETTIER_VERSION}

.PHONY: all
all: deps lib docs test

./depends/${PRETTIER_RELATIVE_DIR}:
	mkdir -p ./build/deps
	mkdir -p ./depends
	cd ./build/deps && \
	git clone https://github.com/Z-snails/prettier && \
	cd prettier && \
	${IDRIS2} --build prettier.ipkg && \
	cp -R ./build/ttc ../../../depends/${PRETTIER_RELATIVE_DIR}/

.PHONY: deps
deps: ./depends/${PRETTIER_RELATIVE_DIR}

.PHONY: clean-install
clean-install: clean install

.PHONY: clean-install-with-src
clean-install-with-src: clean install-with-src

.PHONY: lib
lib:
	${IDRIS2} --build ${lib_pkg}

.PHONY: docs
docs:
	${IDRIS2} --build ${docs_pkg}

.PHONY: test
test:
	${IDRIS2} --build ${test_pkg}
	build/exec/elab-util-test

.PHONY: install
install:
	${IDRIS2} --install ${lib_pkg}

.PHONY: install-with-src
install-with-src:
	${IDRIS2} --install-with-src ${lib_pkg}

.PHONY: clean
clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${test_pkg}
	${IDRIS2} --clean ${docs_pkg}
	${RM} -r depends
	${RM} -r build

# Start a REPL in rlwrap
.PHONY: repl
repl:
	rlwrap -pGreen ${IDRIS2} --find-ipkg src/Language/Reflection/Pretty.idr

# Typecheck after ever file change
.PHONY: develop
develop:
	find -name "*.idr" | entr -d idris2 --typecheck ${lib_pkg}
