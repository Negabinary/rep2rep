SHELL := /bin/bash
MLC=polyc
ifeq (, $(shell which rlwrap))
	REPL=poly
else
	REPL=rlwrap poly
endif
FLAGS=
REP2REP_TMP:=$(shell mktemp)
TEST_TMP:=$(shell mktemp)
REP2REP_VERSION:=$(shell git describe --all --long | rev | cut -d'-' -f 1 | rev)

all: rep2rep
rep2rep: dist/rep2rep

dist/rep2rep: $(REP2REP_TMP)
	mkdir -p dist
	$(MLC) $(FLAGS) -o $@ src/main.sml

test: tests/test
	$<

tests/test: $(TEST_TMP)
	$(MLC) $(FLAGS) -o $@ $<

.PHONY:$(TEST_TMP)
$(TEST_TMP): base.sml tests/tests.sml
	echo "use\""$<"\";" >> $@;
	for f in $(filter-out base.sml,$^); do \
		tmp=$$(dirname $$f)/$$(basename $$f); \
		tmp=$$(sed "s/^src\///" <<< $$tmp); \
		echo "use \"$$tmp\";" >> $@ ; \
	done

.PHONY:clean
clean:
	rm -rf dist
	rm -rf base.sml

.PHONY:repl
repl: src/main.sml
	$(REPL) --use $<
