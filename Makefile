all:
	make -C utils all
	ocamlc -c ast.ml
	menhir --infer --explain parser.mly
	ocamlc -c parser.mli
	ocamlc -c parser.ml
	ocamllex lexer.mll
	ocamlc -c lexer.ml
	ocamlc -c print.ml
	ocamlc -I utils -c utils.cma typechecker.ml
	ocamlc -I utils -c utils.cma expr.ml
	ocamlc -c formula.ml
	ocamlc -c dep.ml
	ocamlc -I utils -c utils.cma interp.ml
	ocamlc -c prove.ml
	ocamlc -c main.ml
	ocamlc -I utils -o sctlprov2 utils.cma ast.cmo parser.cmo lexer.cmo print.cmo typechecker.cmo expr.cmo formula.cmo dep.cmo interp.cmo prove.cmo main.cmo

opt:
	make -C utils opt
	ocamlopt -c ast.ml
	menhir --infer --explain parser.mly
	ocamlopt -c parser.mli
	ocamlopt -c parser.ml
	ocamllex lexer.mll
	ocamlopt -c lexer.ml
	ocamlopt -c print.ml
	ocamlopt -I utils -c utils.cmxa typechecker.ml
	ocamlopt -I utils -c utils.cmxa expr.ml
	ocamlopt -c formula.ml
	ocamlopt -c dep.ml
	ocamlopt -I utils -c utils.cmxa interp.ml
	ocamlopt -c prove.ml
	ocamlopt -c main.ml
	ocamlopt -I utils -o sctlprov2 utils.cmxa ast.cmx parser.cmx lexer.cmx print.cmx typechecker.cmx expr.cmx formula.cmx dep.cmx interp.cmx prove.cmx main.cmx


debug:
	make -C utils all
	ocamlc -g -c ast.ml
	menhir --infer --explain parser.mly
	ocamlc -g -c parser.mli
	ocamlc -g -c parser.ml
	ocamllex lexer.mll
	ocamlc -g -c lexer.ml
	ocamlc -g -c print.ml
	ocamlc -I utils -g -c utils.cma typechecker.ml
	ocamlc -I utils -g -c utils.cma expr.ml
	ocamlc -g -c formula.ml
	ocamlc -g -c dep.ml
	ocamlc -I utils -g -c utils.cma interp.ml
	ocamlc -g -c prove.ml
	ocamlc -g -c main.ml
	ocamlc -I utils -g -o sctlprov2 utils.cma ast.cmo parser.cmo lexer.cmo print.cmo typechecker.cmo expr.cmo formula.cmo dep.cmo interp.cmo prove.cmo main.cmo

lib:
	make -C utils all

lib-opt:
	make -C utils opt

clean:
	make -C utils clean
	rm -f lexer.ml
	rm -f parser.mli
	rm -f parser.ml
	rm -f *.cm[ioxa]
	rm -f *.o
	rm -f sctlprov2
	rm -f ./examples/*.typed
	rm -f ./examples/*.origin