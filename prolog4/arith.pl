:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::']).
:- op(500, yfx, ['$', !]).
term_expansion((A where B), (A :- B)).

m(M) :- M = true
      ; M = false
      ; M = if(M1,M2,M3), m(M1), m(M2), m(M3)
      ; M = zero
      ; M = succ(M1)    , m(M1)
      ; M = pred(M1)    , m(M1)
      ; M = iszero(M1)  , m(M1)
      .

n(zero).
n(succ(M1))                            where n(M1).

v(true).
v(false).
v(M)                                   where n(M).

eval1(if(true, M2, _), M2).
eval1(if(false, _, M3), M3).
eval1(if(M1, M2, M3), if(M1_, M2, M3)) where eval1(M1, M1_).
eval1(succ(M1), succ(M1_))             where eval1(M1, M1_).
eval1(pred(zero), zero).
eval1(pred(succ(N1)), N1)              where n(N1).
eval1(pred(M1), pred(M1_))             where eval1(M1, M1_).
eval1(iszero(zero), true).
eval1(iszero(succ(N1)), false)         where n(N1).
eval1(iszero(M1), iszero(M1_))         where eval1(M1, M1_).

eval(M, M_)                            where eval1(M, M1), eval(M1, M_).
eval(M, M).

run(eval(M), Γ, Γ) :- !, m(M),!,writeln(ok), eval(M, M_), !, writeln(M_).
run(Ls)            :- foldl(run, Ls, [], _).

:- run([eval(true)]).
:- run([eval(if(false, true, false))]).
:- run([eval(zero)]).
:- run([eval(succ(pred(zero)))]).
:- run([eval(iszero(pred(succ(succ(zero)))))]).
:- run([eval(iszero(pred(pred(succ(succ(zero))))))]).
:- run([eval(iszero(zero))]).
:- run([eval(if(zero, succ(pred(zero)), zero))]).
:- run([eval(if(zero, succ(succ(zero)), zero))]).
:- run([eval(if(zero, succ(pred(succ(zero))), zero))]).
:- halt.

