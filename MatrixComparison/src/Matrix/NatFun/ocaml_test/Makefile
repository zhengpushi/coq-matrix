

mat_test.exe : mat_test.ml mat.cmo inv.cmo
	-@rm -f *.mli
	ocamlc.opt.exe -o mat_test.exe mat.cmo inv.cmo $<

%.cmo : %.ml
	ocamlc.opt.exe -o $@ -c $<

# %.cmi : %.mli
# 	ocamlc.opt.exe -o $@ -c $<

exec: mat_test.exe
	./mat_test.exe

clean:
	rm -f *.cmo *.cmi