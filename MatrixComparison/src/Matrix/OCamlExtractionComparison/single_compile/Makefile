
test : test.ml mymatrix.ml
	ocamlc -c mymatrix.mli
	ocamlfind ocamlc -o test -linkpkg mymatrix.ml -package unix

clean :
	rm -f test test.opt *.cmi *.cmo *.o

.PHONY : clean
