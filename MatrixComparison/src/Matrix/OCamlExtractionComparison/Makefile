
matrix : matrix.ml
	@ocamlc -c matrix.mli
	@ocamlfind ocamlc -o $@ -linkpkg matrix.ml -package unix

clean :
	rm -f matrix *.cmi *.cmo *.o

.PHONY : clean
