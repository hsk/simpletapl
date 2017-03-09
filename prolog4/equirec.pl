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
x ::= atom.
t ::= (t -> t) | rec(x, t) | x.
m ::= x | (fn(x : t) -> m) | m $ m.
v ::= fn(x : t) -> m.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
rec(X, T1)![(J -> S)] tsubst rec(X, T1_) :- T1![X, (J -> S)] tsubst2 T1_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
Γ /- (fn(X) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
compute(Γ, rec(X, S1), T) :- S1![(X -> rec(X, S1))] tsubst T.
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T :- teq([], Γ, S, T).
teq(Seen, Γ, S, T) :- member((S, T), Seen).
teq(Seen, Γ, X, Y) :- x(X), x(Y).
teq(Seen, Γ, (S1 -> S2), (T1 -> T2)) :- teq(Seen, Γ, S1, T1), teq(Seen, Γ, S2, T2).
teq(Seen, Γ, rec(X, S1), T) :- S = rec(X, S1), S1![(X -> S)] tsubst S1_, teq([(S, T) | Seen], Γ, S1_, T).
teq(Seen, Γ, S, rec(X, T1)) :- T = rec(X, T1), T1![(X -> T)] tsubst T1_, teq([(S, T) | Seen], Γ, S, T1_).
Γ /- X : T where x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, Γ /- M2 : T2, simplify(Γ, T1, (T11 -> T12)), Γ /- T2 = T11.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar, '').
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval((fn(f : rec('X', ('A' -> 'A'))) -> (fn(x : 'A') -> f $ x)))]).
:- run([eval((fn(x : 'T') -> x))]).
:- run([bind('T', bTVar), bind(i, bVar('T')), eval(i)]).
:- halt.

