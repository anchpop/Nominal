PACKAGE=nominal
HACKAGE_USER=PeterSelinger
SHELL=/bin/bash

VERSION=$(shell grep ^version: ${PACKAGE}.cabal | sed 's/version://;s/[[:space:]]//g')

all: build doc

build: dist/setup/setup
	cabal build

doc: dist/setup/setup
	cabal haddock --hyperlink-source --html-location='http://hackage.haskell.org/package/$$pkg/docs'

doc-for-upload: ${PACKAGE}-${VERSION}-docs.tar.gz

${PACKAGE}-${VERSION}-docs.tar.gz: doc
	rm -rf ${PACKAGE}-${VERSION}-docs
	cp -rp dist/doc/html/${PACKAGE} ${PACKAGE}-${VERSION}-docs
	echo '<meta HTTP-EQUIV="REFRESH" content="0; url=http://hackage.haskell.org/package/${PACKAGE}-${VERSION}">' > ${PACKAGE}-${VERSION}-docs/index.html
	echo 'If your browser does not take you there automatically, please go to' >> ${PACKAGE}-${VERSION}-docs/index.html
	echo '<a href=http://hackage.haskell.org/package/${PACKAGE}-${VERSION}>http://hackage.haskell.org/package/${PACKAGE}-${VERSION}</a>.' >> ${PACKAGE}-${VERSION}-docs/index.html
	tar -Hustar -zcf ${PACKAGE}-${VERSION}-docs.tar.gz ${PACKAGE}-${VERSION}-docs

doc-upload: ${PACKAGE}-${VERSION}-docs.tar.gz
	echo -n "Hackage password for ${HACKAGE_USER}: "; read -s PASSWORD; echo; curl -X PUT -H 'Content-Type: application/x-tar' -H 'Content-Encoding: gzip' --data-binary @${PACKAGE}-${VERSION}-docs.tar.gz https://${HACKAGE_USER}:$$PASSWORD@hackage.haskell.org/package/${PACKAGE}-${VERSION}/docs

doc-upload-candidate: ${PACKAGE}-${VERSION}-docs.tar.gz
	echo -n "Hackage password for ${HACKAGE_USER}: "; read -s PASSWORD; echo; curl -X PUT -H 'Content-Type: application/x-tar' -H 'Content-Encoding: gzip' --data-binary @${PACKAGE}-${VERSION}-docs.tar.gz https://${HACKAGE_USER}:$$PASSWORD@hackage.haskell.org/package/${PACKAGE}-${VERSION}/candidate/docs

install: dist/setup/setup
	cabal install

.PHONY: dist

dist: dist/setup/setup
	cabal sdist

conf dist/setup/setup: ${PACKAGE}.cabal
	cabal configure

doc-for-spellcheck:
	mkdir -p dist
	haddock -o dist/doc-for-spellcheck -h examples/*.hs

examples-clean:
	rm -f examples/*.o examples/*.hi

clean: examples-clean
	cabal clean
	rm -rf ${PACKAGE}-${VERSION}-docs
	rm -f ${PACKAGE}-${VERSION}-docs.tar.gz

spellcheck: doc-for-spellcheck
	ispell -d canadian -p local/dictionary.txt -H dist/doc-for-spellcheck/*.html ChangeLog *cabal README.md
