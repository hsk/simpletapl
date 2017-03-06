:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::']).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
term_expansion((A where B), (A :- B)).
:- style_check(- singleton).
val(X) :- X \= bool, X \= top, X \= true, X \= false, atom(X).
l(L) :- atom(L) ; integer(L).
t(T) :- T = bool ; T = top ; T = (T1 -> T2), t(T1), t(T2) ; T = {Tf}, maplist([X : T1] >> (l(X), t(T1)), Tf).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = X, val(X) ; M = (fn(X : T1) -> M1), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = {Tf}, maplist([X = M1] >> (l(X), m(M1)), Mf) ; M = proj(M1, L), m(M1), l(L).
true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
J![(J -> M)] subst M :- val(J).
X![(J -> M)] subst X :- val(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
proj(M1, L)![(J -> M)] subst proj(M1_, L) :- M1![(J -> M)] subst M1_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
v(true).
v(false).
v((fn(_ : _) -> _)).
v({Mf}) :- maplist([L = M] >> v(M), Mf).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- proj({Mf}, L) ==> M where member(L = M, Mf).
Γ /- proj(M1, L) ==> proj(M1_, L) where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
Γ /- T <: T.
Γ /- _ <: top.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ /- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ /- S /\ T : U :- halt.
Γ /- S \/ T : U :- halt.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T where halt.
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- proj(M1, L) : T where Γ /- M1 : {Tf}, member(L : T, Tf).
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind_, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(r : {[x : (top -> top)]}) -> proj(r, x) $ proj(r, x)) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]})]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval({[x = true, y = false]})]).
:- run([eval(proj({[x = true, y = false]}, x))]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval(proj({[1 = true, 2 = false]}, 1))]).
:- run([eval(if(true, {[x = true, y = false, a = false]}, {[y = false, x = {[]}, b = false]}))]).
:- halt.

