.PHONY: default

TMP := $(shell mktemp -u)

INPUTS   = $(wildcard tests/fixtures/*.asm)
OUTPUTS  = $(INPUTS:.asm=.hack)
OUTPUTS := $(foreach output,$(OUTPUTS),$(TMP)/$(notdir $(value output)))

default: $(OUTPUTS)

$(TMP):
	mkdir -p $@

$(TMP)/%.hack: tests/fixtures/%.asm tests/fixtures/%.hack $(TMP)
	cargo run -q -- --text -o $@ $<
	diff $@ $(patsubst %.asm,%.hack,$<)
