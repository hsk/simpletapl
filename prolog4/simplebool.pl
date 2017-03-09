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
:- style_check(- singleton).
:- use_module(rtg).
w ::= bool | true | false.
syntax(x).
x(X) :- \+ w(X), atom(X).
t ::= bool | nat | x | (t -> t).
m ::= true | false | if(m, m, m) | 0 | succ(m) | pred(m) | iszero(m) | x | (fn(x : t) -> m) | m $ m.
v ::= true | false | (fn(x : t) -> m).
true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
A![(J -> M)] subst B :- writeln(error : A![(J -> M)] subst B), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : bool, Γ /- M2 : T2, Γ /- M3 : T2.
Γ /- X : T where x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T11.
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M ==>> M_, !, Γ /- M_ : T, !, writeln(M_ : T).
run(bind(X, T), Γ, [X - bVar(T) | Γ]) :- !, writeln(X : T).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn(x : bool) -> x)), eval((fn(x : bool) -> (fn(x : bool) -> x))), eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true))), bind(a, bool), eval(a), eval((fn(x : bool) -> x) $ a), eval((fn(x : bool) -> (fn(x : bool) -> x) $ x) $ a), eval((fn(x : bool) -> x) $ true), eval((fn(x : bool) -> (fn(x : bool) -> x) $ x) $ true)]).
:- halt.

