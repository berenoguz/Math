.PHONY: check

SRC=$(wildcard Math/*.agda)

check: $(SRC)

%.agda: FORCE
	agda --safe --without-K $@

FORCE:
