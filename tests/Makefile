OCAMLFIND ?= ocamlfind
OCAMLOPTC ?= "$(OCAMLFIND)" opt
ROCQ_KERNEL := $(shell "$(OCAMLFIND)" query rocq-runtime.kernel 2>/dev/null)

all: coc

coc: core.ml core.mli top.ml newman.coc
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c core.mli
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c core.ml
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c -pp "camlp4o" top.ml
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -o coc uint63.cmx pstring.cmx core.cmx top.cmx
	@echo '***** test: checking the proof of the Newman lemma *****'
	./coc < newman.coc
	@echo '******************** End of test ***********************'

clean:
	rm -f core.ml core.mli *.cmx *.cmi *.o

# Building core.ml : we do not want an Extract.vo to be produced
core.ml core.mli: Extract.v
	$(COQBIN)rocq compile -R ../theories CoqInCoq Extract.v

.PHONY: all clean
