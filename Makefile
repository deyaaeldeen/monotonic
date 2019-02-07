MONOREF_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

### libraries
lib: lib/stdlib++/.git

lib/stdlib++/.git:
	git submodule update --init lib/stdlib++
	echo "standard-library++" >> $(HOME)/.agda/defaults
	echo "$(MONOREF_DIR)/lib/stdlib++/.agda-lib" >> $(HOME)/.agda/libraries

.PHONY: assumptions
assumptions:
	git grep --color -Hi "postulate" -- "MonoRef/**/*.agda"
	git grep --color -Hi "TERMINATING" -- "MonoRef/**/*.agda"

### cleaning
.PHONY: clean clean-all
clean:
	-cd MonoRef && find . -iname '*.agdai' -exec rm {} \;
