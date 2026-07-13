PAPER = main
SLIDES = slides

.PHONY: all slides clean

all: $(PAPER).pdf

slides: $(SLIDES).pdf

$(PAPER).pdf: $(PAPER).tex references.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(PAPER).tex

# Metropolis (mtheme) needs a Unicode engine for Fira fonts. Use LuaLaTeX,
# NOT XeLaTeX: with the default show-notes (pgfpages) layout, XeLaTeX leaks
# beamer's overlay-transparency state across the double-width pages, which
# renders all base-layer slide text nearly invisible.
$(SLIDES).pdf: $(SLIDES).tex
	latexmk -lualatex -interaction=nonstopmode -halt-on-error $(SLIDES).tex \
	  || latexmk -pdf -interaction=nonstopmode -halt-on-error $(SLIDES).tex

clean:
	latexmk -C $(PAPER).tex
	latexmk -C $(SLIDES).tex
	rm -f $(PAPER).bbl
