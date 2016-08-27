IDRIS := idris
PKG   := alice

PANDOC   := @pandoc -f markdown_github+lhs -t markdown_github
SED_HACK := sed 's/ sourceCode/idris/'

MDS = out/01-TheFirstTale.md

.PHONY: build clean clean-all install rebuild doc doc-clean test

all: build out

build:
	@$(IDRIS) --build $(PKG).ipkg

clean:
	@$(IDRIS) --clean $(PKG).ipkg
	@find . -name '*.ibc' -delete

clean-all: clean doc-clean

install:
	@$(IDRIS) --install $(PKG).ipkg

rebuild: clean build

doc: build
	@$(IDRIS) --mkdoc $(PKG).ipkg

doc-clean:
	@rm -rf $(PKG)_doc/*
	@touch $(PKG)_doc/IdrisDoc

test:
	@$(IDRIS) --testpkg $(PKG).ipkg

out: $(MDS)

out/01-TheFirstTale.md: src/WhoStoleTheTarts/TheFirstTale.lidr
	$(PANDOC) $< | $(SED_HACK) > $@
