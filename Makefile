all: lrat2dk debug_printers.cmo cleandk lrat2dk.opt

OCAMLCFLAGS= -g
OCAMLOPTFLAGS= -noassert -nodynlink -O3 -unsafe -ppx ./ppx_remove_debug
%.ml: %.mll
	ocamllex $<

lrat_lexer.cmo: ptset.cmi
dimacs_lexer.cmo: ptset.cmi
ptset.cmo: ptset.cmi
globals.cmo: globals.cmi

%.cmo: %.ml
	ocamlc $(OCAMLCFLAGS) -c $<

%.cmx: %.ml
	ocamlopt $(OCAMLOPTFLAGS) -c $<

%.cmi: %.mli
	ocamlc -c $<

OBJ=ptset.cmo lrat_types.cmo globals.cmo dimacs_lexer.cmo lrat_lexer.cmo ipl.cmo lrat_ipl.cmo proof_generation.cmo

lrat2dk: $(OBJ)
	ocamlc $(OCAMLCFLAGS) -o $@ $(OBJ)

lrat2dk.opt: ppx_remove_debug $(OBJ:.cmo=.cmx)
	ocamlopt $(OCAMLOPTFLAGS) -o $@ $(OBJ:.cmo=.cmx)

cleandk: analyse_lexer.cmo filter_lexer.cmo cleandk.cmo
	ocamlc $(OCAMLCFLAGS) -o $@ $^

ppx_remove_debug: ppx_remove_debug.ml
	ocamlfind ocamlc -package ppx_tools.metaquot -o $@ -I +compiler-lib ocamlcommon.cma $<

clean:
	-rm *.cmo *.cmi lrat2dk

depend:
	ocamldep *.ml *.mli > .depend

test:
	-mv examples/*.dk examples/backups/
	sh ./test.sh 2> log_tests
	for i in examples/*.dk; do echo "Checking $$i"; dkcheck $$i; done

include .depend
