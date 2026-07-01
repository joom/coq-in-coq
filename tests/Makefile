OCAMLFIND ?= ocamlfind
OCAMLOPTC ?= "$(OCAMLFIND)" opt
ROCQ_KERNEL := $(shell "$(OCAMLFIND)" query rocq-runtime.kernel 2>/dev/null)

all: coc

coc: core.ml core.mli lexer.mll parser.mly top.ml newman.coc
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c core.mli
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c core.ml
	menhir --infer --ocamlc '$(OCAMLFIND) ocamlc -I $(ROCQ_KERNEL)' parser.mly
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c parser.mli
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c parser.ml
	ocamllex lexer.mll
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c lexer.ml
	$(OCAMLOPTC) -I "$(ROCQ_KERNEL)" -c top.ml
	$(OCAMLFIND) opt -package rocq-runtime.kernel -linkpkg -o coc core.cmx parser.cmx lexer.cmx top.cmx
	@echo '***** test: checking the proof of the Newman lemma *****'
	./coc < newman.coc
	@echo '******************** End of test ***********************'

clean:
	rm -f core.ml core.mli parser.ml parser.mli parser.conflicts lexer.ml *.cmx *.cmi *.o coc

# Building core.ml : we do not want an Extract.vo to be produced
core.ml core.mli: Extract.v
	$(COQBIN)rocq compile -R ../theories CoqInCoq Extract.v

.PHONY: all clean
