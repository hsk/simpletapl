:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::', '#', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
term_expansion((A where B), (A :- B)).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = 0 ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1).
n(N) :- N = 0 ; N = succ(N1), n(N1).
v(V) :- V = true ; V = false ; n(V).
if(true, M2, _) ==> M2.
if(false, _, M3) ==> M3.
if(M1, M2, M3) ==> if(M1_, M2, M3) where M1 ==> M1_.
succ(M1) ==> succ(M1_) where M1 ==> M1_.
pred(0) ==> 0.
pred(succ(N1)) ==> N1 where n(N1).
pred(M1) ==> pred(M1_) where M1 ==> M1_.
iszero(0) ==> true.
iszero(succ(N1)) ==> false where n(N1).
iszero(M1) ==> iszero(M1_) where M1 ==> M1_.
M ==>> M_ where M ==> M1, M1 ==>> M_.
M ==>> M.
run(eval(M), Γ, Γ) :- !, m(M), !, M ==>> M_, !, writeln(M_).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval(true)]).
:- run([eval(if(false, true, false))]).
:- run([eval(0)]).
:- run([eval(succ(pred(0)))]).
:- run([eval(iszero(pred(succ(succ(0)))))]).
:- run([eval(iszero(pred(pred(succ(succ(0))))))]).
:- run([eval(iszero(0))]).
:- run([eval(if(0, succ(pred(0)), 0))]).
:- run([eval(if(0, succ(succ(0)), 0))]).
:- run([eval(if(0, succ(pred(succ(0))), 0))]).
:- halt.

