all:
	ocamlc -c options.ml
	ocamlc -c pairs.ml
	ocamlc -c refpairs.ml
	ocamlc -a -o utils.cma options.cmo pairs.cmo refpairs.cmo

clean:
	rm -f *.cm[ioxa]
	rm -f utils.cma