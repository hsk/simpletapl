test: build
	./f test.f > test_result.txt
	cat test_result.txt
	diff test_result.txt test_expected.txt
	./f -p test.f > test.pl
gen: build
	./f test.f > test_expected.txt
	cat test_expected.txt
build: f

f: parser.mly lexer.mll *.ml
	ocamlyacc parser.mly
	rm -rf parser.mli
	ocamllex lexer.mll
	ocamlc -g syntax.ml parser.ml lexer.ml core.ml prolog.ml main.ml -o f
	rm -rf *.cm* parser.ml lexer.ml
clean:
	rm -rf *.cm* parser.ml lexer.ml f test_result.txt

