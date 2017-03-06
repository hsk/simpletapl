:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::']).
:- op(500, yfx, ['$', !]).
term_expansion((A where B), (A :- B)).
:- style_check(- singleton).
val(X) :- atom(X).
k(K) :- K = '*' ; K = kArr(K1, K2), k(K1), k(K2).
t(T) :- T = X, val(X) ; T = (T1 -> T2), t(T1), t(T2) ; T = all(X, K, T1), val(X), k(K), t(T1) ; T = abs(TX, K, T2), val(TX), k(K), t(T2) ; T = T1 $ T2, t(T1), t(T2).
m(M) :- M = X, val(X) ; M = (fn(X : T1) -> M1), val(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = (fn(TX :: K) => M2), val(TX), k(K), m(M2) ; M = M1![T2], m(M1), t(T2).
tsubst(J, S, J, S) :- val(J).
tsubst(J, S, X, X) :- val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_)) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, all(TX, K, T2), all(TX, K, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, abs(TX, K, T2), abs(TX, K, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, T1 $ T2, T1_ $ T2_) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, T, T_) :- writeln(error : tsubst(J, S, T, T_)), halt.
tsubst2(X, X, S, T, T).
tsubst2(X, J, S, T, T_) :- tsubst(J, S, T, T_).
subst(J, M, J, M) :- val(J).
subst(J, M, (fn(X1 : T1) -> M2), (fn(X1 : T1) -> M2_)) :- subst2(X1, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, (fn(TX :: K) => M2), (fn(TX :: K) => M2_)) :- subst(J, M, M2, M2_).
subst(J, M, M1![T2], M1_![T2]) :- subst(J, M, M1, M1_).
subst(J, M, M1, M1).
subst(J, M, A, B) :- writeln(error : subst(J, M, A, B)), fail.
subst2(X, X, M, T, T).
subst2(X, J, M, T, T_) :- subst(J, M, T, T_).
tmsubst(J, S, X, X) :- val(X).
tmsubst(J, S, (fn(X : T1) -> M2), (fn(X : T1_) -> M2_)) :- tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, M1 $ M2, M1_ $ M2_) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, (fn(TX :: K) => M2), (fn(TX :: K) => M2_)) :- tmsubst2(TX, J, S, M2, M2_).
tmsubst(J, S, M1![T2], M1_![T2_]) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T2, T2_).
tmsubst2(X, X, S, T, T).
tmsubst2(X, J, S, T, T_) :- tmsubst(J, S, T, T_).
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
v((fn(_ : _) -> _)).
v((fn(_ :: _) => _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), subst(X, V2, M12, R).
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where tmsubst(X, T2, M11, M11_).
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
compute(Γ, abs(X, _, T12) $ T2, T) :- tsubst(X, T2, T12, T).
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- all(TX1, K1, S2) == all(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- abs(TX1, K1, S2) == abs(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ \- T :: K where Γ /- T :: K, !.
Γ \- T :: K where writeln(error : kindof(T, K)), fail.
Γ /- X :: '*' where val(X), \+ member(X - _, Γ).
Γ /- X :: K where val(X), !, getb(Γ, X, bTVar(K)).
Γ /- (T1 -> T2) :: '*' where !, Γ \- T1 :: '*', Γ \- T2 :: '*'.
Γ /- all(TX, K1, T2) :: '*' where !, [TX - bTVar(K1) | Γ] \- T2 :: '*'.
Γ /- abs(TX, K1, T2) :: kArr(K1, K) where !, [TX - bTVar(K1) | Γ] \- T2 :: K.
Γ /- T1 $ T2 :: K12 where !, Γ \- T1 :: kArr(K11, K12), Γ \- T2 :: K11.
Γ /- T :: '*'.
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ \- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (fn(TX :: K1) => M2) : all(TX, K1, T2) where [TX - bTVar(K1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ \- T2 :: K2, Γ /- M1 : T1, simplify(Γ, T1, all(X, K2, T12)), tsubst(X, T2, T12, T12_).
Γ /- M : _ where writeln(error : typeof(M)), !, halt.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(K1), R) :- swritef(R, ' :: %w', [K1]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S), !.
run(Ls) :- foldl(run, Ls, [], Γ).
:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x))![all('X', '*', ('X' -> 'X'))])]).
:- run([bind('T', bTVar('*')), bind(k, bVar('T'))]).
:- run([bind('TT', bTVar(kArr('*', '*'))), bind(kk, bVar('TT'))]).
:- run([bind('T', bTVar('*')), bind(x, bVar(abs('X', kArr('*', '*'), 'T') $ 'T'))]).
:- halt.

