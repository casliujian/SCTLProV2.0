all:
	ocamlc -c options.ml
	ocamlc -c pairs.ml
	ocamlc -c refpairs.ml
	ocamlc -a -o utils.cma options.cmo pairs.cmo refpairs.cmo

opt:
	ocamlopt -c options.ml
	ocamlopt -c pairs.ml
	ocamlopt -c refpairs.ml
	ocamlopt -a -o utils.cmxa options.cmx pairs.cmx refpairs.cmx


clean:
	rm -f *.cm[ioxa]
	rm -f *.a
	rm -f *.o
	rm -f utils.cma
	rm -f utils.cmxa