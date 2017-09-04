all:
	make -C utils all
	ocamlc -c ast.ml
	ocamlc -c print.ml
	menhir --infer --explain parser.mly
	ocamlc -I utils -c utils.cma parser.mli
	ocamlc -I utils -c utils.cma parser.ml
	ocamllex lexer.mll
	ocamlc -c lexer.ml
	ocamlc -I utils -c utils.cma typechecker.ml
	ocamlc -I utils -c utils.cma expr.ml
	ocamlc -c formula.ml
	ocamlc -c dep.ml
	ocamlc -I utils -c utils.cma interp.ml
	ocamlc -I utils -c utils.cma prover.ml
	ocamlfind ocamlc -thread threads.cma -c communicate.ml -package yojson -linkpkg -g
	ocamlfind ocamlc -thread threads.cma -I utils -c utils.cma prover_visualization.ml
	ocamlc -c main.ml
	ocamlfind ocamlc -thread threads.cma -I utils -o sctlprov2 utils.cma -package yojson -linkpkg -g ast.cmo print.cmo parser.cmo lexer.cmo \
	 typechecker.cmo expr.cmo formula.cmo dep.cmo interp.cmo prover.cmo communicate.cmo prover_visualization.cmo main.cmo

win:
	make -C utils all
	ocamlc -c ast.ml
	ocamlc -c print.ml
	menhir --infer --explain parser.mly
	ocamlc -I utils -c utils.cma parser.mli
	ocamlc -I utils -c utils.cma parser.ml
	ocamllex lexer.mll
	ocamlc -c lexer.ml
	ocamlc -I utils -c utils.cma typechecker.ml
	ocamlc -I utils -c utils.cma expr.ml
	ocamlc -c formula.ml
	ocamlc -c dep.ml
	ocamlc -I utils -c utils.cma interp.ml
	ocamlc -I utils -c utils.cma prover.ml
	ocamlfind ocamlc -thread threads.cma -c communicate.ml -package yojson -linkpkg -g
	ocamlfind ocamlc -thread threads.cma -I utils -c utils.cma prover_visualization.ml
	ocamlc -c main.ml
	ocamlfind ocamlc -thread threads.cma -I utils -o sctlprov2.exe utils.cma -package yojson -linkpkg -g ast.cmo print.cmo parser.cmo lexer.cmo \
	 typechecker.cmo expr.cmo formula.cmo dep.cmo interp.cmo prover.cmo communicate.cmo prover_visualization.cmo main.cmo


opt:
	make -C utils opt
	ocamlopt -c ast.ml
	ocamlopt -c print.ml
	menhir --infer --explain parser.mly
	ocamlopt -I utils -c utils.cmxa parser.mli
	ocamlopt -I utils -c utils.cmxa parser.ml
	ocamllex lexer.mll
	ocamlopt -c lexer.ml
	ocamlopt -I utils -c utils.cmxa typechecker.ml
	ocamlopt -I utils -c utils.cmxa expr.ml
	ocamlopt -c formula.ml
	ocamlopt -c dep.ml
	ocamlopt -I utils -c utils.cmxa interp.ml
	ocamlopt -I utils -c utils.cmxa prover.ml
	ocamlfind ocamlopt -thread threads.cmxa -c communicate.ml -package yojson -linkpkg -g
	ocamlfind ocamlopt -thread threads.cmxa -I utils -c utils.cmxa prover_visualization.ml
	ocamlopt -c main.ml
	ocamlfind ocamlopt -thread threads.cmxa -I utils -o sctlprov2 utils.cmxa -package yojson -linkpkg -g ast.cmx print.cmx parser.cmx lexer.cmx \
	 typechecker.cmx expr.cmx formula.cmx dep.cmx interp.cmx prover.cmx communicate.cmx prover_visualization.cmx main.cmx


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
	rm -f .origin
	rm -f .typed
	rm -f *.origin
	rm -f *.typed
	rm -f *.conflicts