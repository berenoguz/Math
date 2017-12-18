.PHONY: check

SRC=$(wildcard Math/*.agda)

check: $(SRC)

%.agda: FORCE
	agda $@

FORCE:
