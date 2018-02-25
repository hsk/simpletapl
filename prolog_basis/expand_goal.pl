:- op(1200, xfx, [::=]).
% 項全体の変換定義
term_expansion((A ::= B,C), (A:-B,mark(A,C))) :- assert(memo(A)),writeln(term_expansion(A::=B)).
% ゴール内の１つの項にマッチさせた変換
goal_expansion(mark(A,B),B) :- memo(A),writeln(goal_expansion(A,B)).
hoge ::= test,data.
:- halt.
