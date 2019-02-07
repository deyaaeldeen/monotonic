MONOREF_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

### libraries
lib: lib/stdlib++/.git

lib/stdlib++/.git:
	git submodule update --init lib/stdlib++
	echo "standard-library++" >> $(HOME)/.agda/defaults
	echo "$(MONOREF_DIR)/lib/stdlib++/.agda-lib" >> $(HOME)/.agda/libraries

.PHONY: assumptions
assumptions:
	git grep --color -Hi "postulate" -- "src/**/*.agda"
	git grep --color -Hi "TERMINATING" -- "src/**/*.agda"

### cleaning
.PHONY: clean clean-all
clean:
	-rm Readme.agdai
	-cd MonoRef && find . -iname '*.agdai' -exec rm {} \;
