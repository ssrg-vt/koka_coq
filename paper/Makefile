SRC:=$(wildcard *.tex *.bib *.sty *.cls sections/*.tex figures/*.tex figures/*.png code/*.tex)

OUT:=.out
BACKLINK:=$(OUT)/main.pdf

LATEXMK:=latexmk -halt-on-error -pdf -output-directory=$(OUT)

.SUFFIXES: .pdf .asy

all: main.pdf

$(BACKLINK):
	mkdir -p $(OUT)
	$(RM) $(BACKLINK)
	ln -s '../main.pdf' $(BACKLINK)

main.pdf: $(SRC) $(BACKLINK)
	$(LATEXMK) main

clean:
	$(LATEXMK) -c main
	$(RM) -r $(OUT)
	$(RM) 'main.dvi' 'main.log' 'main.out' 'main.synctex.gz' 'main.aux'
