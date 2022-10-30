all: aritha rapport

aritha: x86_64.ml lecture_fichier.ml analyse.ml compilateur.ml
	ocamlc x86_64.ml lecture_fichier.ml analyse.ml compilateur.ml -o Aritha
	./Aritha

rapport: rapport.tex
	pdflatex rapport.tex

compile_assembleur:
	gcc -no-pie print.s -o exc
	./exc