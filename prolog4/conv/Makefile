all:
	ocamlyacc parser.mly
	rm -rf parser.mli
	ocamllex lexer.mll
	ocamlc str.cma syntax.ml parser.ml lexer.ml conv.ml main.ml -o conv
	rm -rf *.mli *.cm* parser.ml lexer.ml
	./conv -varbose test.pl

clean:
	rm -rf *.mli *.cm* conv parser.ml lexer.ml
	rm -rf result.txt expected.txt
