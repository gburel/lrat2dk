all: lrat2dk

%.ml: %.mll
	ocamllex $<

lrat_lexer.cmo: ptset.cmi
dimacs_lexer.cmo: ptset.cmi
ptset.cmo: ptset.cmi
globals.cmo: globals.cmi

%.cmo: %.ml
	ocamlc -c $<

%.cmi: %.mli
	ocamlc -c $<

lrat2dk: ptset.cmo lrat_types.cmo globals.cmo dimacs_lexer.cmo lrat_lexer.cmo ipl.cmo lrat_ipl.cmo proof_generation.cmo
	ocamlc -o $@ $^
clean:
	-rm *.cmo *.cmi lrat2dk

depend:
	ocamldep *.ml *.mli > .depend

include .depend
