# :- style_check(-singleton).

run:
	swipl arith.pl > results/arith_result.txt
	diff results/arith_result.txt results/arith_expected.txt
	swipl untyped.pl > results/untyped_result.txt
	diff results/untyped_result.txt results/untyped_expected.txt
	swipl fulluntyped.pl > results/fulluntyped_result.txt
	diff results/fulluntyped_result.txt results/fulluntyped_expected.txt

gen:
	swipl arith.pl > results/arith_expected.txt
	swipl untyped.pl > results/untyped_expected.txt
	swipl fulluntyped.pl > results/fulluntyped_expected.txt
clean:
	rm results/*_result.txt
