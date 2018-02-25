:- op(1200, xfx, [::=]).
term_expansion((A ::= B,C), (A:-B,mark(A,C))) :- writeln(term_expansion(A::=B)),assert(memo(A)).
goal_expansion(mark(A,B),B) :- memo(A),writeln(goal_expansion(A,B)).
hoge ::= test,data.
:- halt.

