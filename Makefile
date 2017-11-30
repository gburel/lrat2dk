all: lrat2dk debug_printers.cmo

OCAMLFLAGS= -g

%.ml: %.mll
	ocamllex $<

lrat_lexer.cmo: ptset.cmi
dimacs_lexer.cmo: ptset.cmi
ptset.cmo: ptset.cmi
globals.cmo: globals.cmi

%.cmo: %.ml
	ocamlc $(OCAMLFLAGS) -c $<

%.cmi: %.mli
	ocamlc -c $<

lrat2dk: ptset.cmo lrat_types.cmo globals.cmo dimacs_lexer.cmo lrat_lexer.cmo ipl.cmo lrat_ipl.cmo proof_generation.cmo
	ocamlc $(OCAMLFLAGS) -o $@ $^
clean:
	-rm *.cmo *.cmi lrat2dk

depend:
	ocamldep *.ml *.mli > .depend

test:
	-rm examples/*.dk
	sh ./test.sh 2> log_tests
	for i in examples/*.dk; do echo "Checking $$i"; dkcheck $$i; done

include .depend
