PAPER = main
SLIDES = slides

.PHONY: all slides clean

all: $(PAPER).pdf

slides: $(SLIDES).pdf

$(PAPER).pdf: $(PAPER).tex references.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(PAPER).tex

# Metropolis (mtheme) renders best with XeLaTeX + Fira fonts; fall back to
# `latexmk -pdf` if xelatex is unavailable.
$(SLIDES).pdf: $(SLIDES).tex
	latexmk -xelatex -interaction=nonstopmode -halt-on-error $(SLIDES).tex \
	  || latexmk -pdf -interaction=nonstopmode -halt-on-error $(SLIDES).tex

clean:
	latexmk -C $(PAPER).tex
	latexmk -C $(SLIDES).tex
	rm -f $(PAPER).bbl
