:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::']).
:- op(500, yfx, ['$', !]).
term_expansion((A where B), (A :- B)).
t(T) :- T = bool ; T = nat.
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = zero ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1).
n(zero).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
eval1(if(true, M2, _), M2).
eval1(if(false, _, M3), M3).
eval1(if(M1, M2, M3), if(M1_, M2, M3)) where eval1(M1, M1_).
eval1(succ(M1), succ(M1_)) where eval1(M1, M1_).
eval1(pred(zero), zero).
eval1(pred(succ(N1)), N1) where n(N1).
eval1(pred(M1), pred(M1_)) where eval1(M1, M1_).
eval1(iszero(zero), true).
eval1(iszero(succ(N1)), false) where n(N1).
eval1(iszero(M1), iszero(M1_)) where eval1(M1, M1_).
eval(M, M_) where eval1(M, M1), eval(M1, M_).
eval(M, M).
typeof(true, bool).
typeof(false, bool).
typeof(if(M1, M2, M3), T2) where typeof(M1, bool), typeof(M2, T2), typeof(M3, T2).
typeof(zero, nat).
typeof(succ(M1), nat) where typeof(M1, nat).
typeof(pred(M1), nat) where typeof(M1, nat).
typeof(iszero(M1), bool) where typeof(M1, nat).
run(eval(M), Γ, Γ) :- !, m(M), !, eval(M, M_), !, typeof(M, T), !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval(true)]).
:- run([eval(if(false, true, false))]).
:- run([eval(zero)]).
:- run([eval(succ(pred(zero)))]).
:- run([eval(iszero(pred(succ(succ(zero)))))]).
:- run([eval(iszero(pred(pred(succ(succ(zero))))))]).
:- run([eval(iszero(zero))]).
:- halt.

