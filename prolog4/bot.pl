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
val(X) :- X \= top, X \= bot, atom(X).
t(T) :- T = (T1 -> T2), t(T1), t(T2) ; T = top ; T = bot.
m(M) :- M = X, val(X) ; M = (fn(X : T1) -> M1), val(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2).
J![(J -> M)] subst M :- val(J).
X![(J -> M)] subst X :- val(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
v((fn(_ : _) -> _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
Γ /- T1 <: T2 where T1 = T2.
Γ /- _ <: top.
Γ /- bot <: _.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- M1 $ M2 : bot where Γ /- M1 : bot, Γ /- M2 : T2.
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : bot) -> x))]).
:- run([eval((fn(x : bot) -> x $ x))]).
:- run([bind(y, bVar((bot -> bot))), bind(x, bVar(bot)), eval(y $ x)]).
:- halt.

