all: aritha assembleur

aritha: x86_64.ml analyse.ml Aritha.ml
	ocamlc x86_64.ml analyse.ml compilateur.ml -o Aritha
	./Aritha
	
assembleur: print.s
	gcc -no-pie print.s -o exc
	./exc
