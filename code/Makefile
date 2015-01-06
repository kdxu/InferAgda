.PHONY: sync all

all: latex/Infer.tex \
     latex/lib.tex \
     latex/Term.tex \

latex/%.tex : %.lagda 
	agda --latex --allow-unsolved-metas -i /Users/kyoko/agda-stdlib-0.8.1/src/ -i . $< 


clean: 
	rm -f *.agdai
	rm -f latex/*.tex
