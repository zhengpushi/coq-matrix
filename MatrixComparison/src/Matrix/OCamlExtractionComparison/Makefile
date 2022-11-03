
OCAMLC := ocamlc

test : test.ml deplist.ml
	ocamlc -c deplist.mli
	ocamlc -c deplist.ml
	ocamlc test.ml -o $@

test.opt : test.ml deplist.ml
	ocamlopt -c deplist.mli
	ocamlopt -c deplist.ml
	ocamlopt test.ml -o $@

clean :
	rm -f test test.opt *.cmi *.cmo *.o

.PHONY : clean
