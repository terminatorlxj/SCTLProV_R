linux: bdd.ml term.ml formula.ml modul.ml prover_recursive.ml prover_recursive_bdd.ml lexer.mll parser.mly main.ml
	ocamllex lexer.mll       
	ocamlyacc parser.mly 
	ocamlfind ocamlopt -o sctl -package cudd -linkpkg -g bdd.ml term.ml formula.ml modul.ml prover_recursive.ml prover_recursive_bdd.ml parser.mli parser.ml lexer.ml main.ml

win: bdd.ml term.ml formula.ml modul.ml prover_recursive.ml prover_recursive_bdd.ml lexer.mll parser.mly main.ml
	ocamllex lexer.mll       
	ocamlyacc parser.mly 
	ocamlfind ocamlopt -o sctl.exe -package cudd -linkpkg -g bdd.ml term.ml formula.ml modul.ml prover_recursive.ml prover_recursive_bdd.ml parser.mli parser.ml lexer.ml main.ml

clean:
	rm -f *.cm[ioax]
	rm -f *.o
	rm -f *.a
	rm -f lexer.ml parser.mli parser.ml
	rm -f *.annot
	rm -f *.bak
	rm -f sctl
	rm -f sctl.exe

