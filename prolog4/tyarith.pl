:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1100, xfy, [in]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::', '#', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
term_expansion((A where B), (A :- B)).
:- use_module(rtg).
t ::= bool | nat.
m ::= true | false | if(m, m, m) | 0 | succ(m) | pred(m) | iszero(m).
n ::= 0 | succ(n).
v ::= true | false | n.
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
typeof(true, bool).
typeof(false, bool).
typeof(if(M1, M2, M3), T2) where typeof(M1, bool), typeof(M2, T2), typeof(M3, T2).
typeof(0, nat).
typeof(succ(M1), nat) where typeof(M1, nat).
typeof(pred(M1), nat) where typeof(M1, nat).
typeof(iszero(M1), bool) where typeof(M1, nat).
run(eval(M), Γ, Γ) :- !, m(M), !, M ==>> M_, !, typeof(M, T), !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval(true)]).
:- run([eval(if(false, true, false))]).
:- run([eval(0)]).
:- run([eval(succ(pred(0)))]).
:- run([eval(iszero(pred(succ(succ(0)))))]).
:- run([eval(iszero(pred(pred(succ(succ(0))))))]).
:- run([eval(iszero(0))]).
:- halt.

