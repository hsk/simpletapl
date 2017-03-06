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
val(X) :- X \= top, atom(X).
k(K) :- K = '*' ; K = kArr(K1, K2), k(K1), k(K2).
t(T) :- T = top ; T = X, val(X) ; T = (T1 -> T2), t(T1), t(T2) ; T = all(X, T1, T2), val(X), t(T1), t(T2) ; T = abs(TX, K, T2), val(TX), k(K), t(T2) ; T = T1 $ T2, t(T1), t(T2).
m(M) :- M = X, val(X) ; M = (fn(X : T1) -> M1), val(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = (fn(TX :: T1) => M2), val(TX), t(T1), m(M2) ; M = M1![T2], m(M1), t(T2).
top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S :- val(J).
X![(J -> S)] tsubst X :- val(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
all(TX, T1, T2)![(J -> S)] tsubst all(TX, T1_, T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
abs(TX, K, T2)![(J -> S)] tsubst abs(TX, K, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![(J -> S)] tsubst T_ :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_.
J![(J -> M)] subst M :- val(J).
X![(J -> M)] subst X :- val(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(fn(TX :: T1) => M2)![(J -> M)] subst (fn(TX :: T1) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
X![(J -> S)] tmsubst X :- val(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(fn(TX :: T1) => M2)![(J -> S)] tmsubst (fn(TX :: T1_) => M2_) :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
maketop('*', top).
maketop(kArr(K1, K2), abs('_', K1, K2_)) :- maketop(K2, K2_).
v((fn(_ : _) -> _)).
v((fn(_ :: _) => _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
compute(Γ, abs(X, _, T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- top == top.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- all(TX, S1, S2) == all(_, T1, T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- abs(TX, K1, S2) == abs(_, K1, T2) :- [TX - bName | g] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !.
Γ /- T :: K where writeln(error : kindof(T, K)), fail.
Γ \- X :: '*' where val(X), \+ member(X - _, Γ).
Γ \- X :: K where val(X), getb(Γ, X, bTVar(T)), Γ /- T :: K.
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- all(TX, T1, T2) :: '*' where !, [TX - bTVar(T1) | Γ] /- T2 :: '*'.
Γ \- abs(TX, K1, T2) :: kArr(K1, K) where !, maketop(K1, T1), [TX - bTVar(T1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: kArr(K11, K12), Γ /- T2 :: K11.
Γ \- T :: '*'.
promote(Γ, X, T) :- val(X), getb(Γ, X, bTVar(T)).
promote(Γ, S $ T, S_ $ T) :- promote(Γ, S, S_).
Γ /- S <: T where Γ /- S = T.
Γ /- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- X <: T where val(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- T1 $ T2 <: T where promote(Γ, T1 $ T2, S), Γ /- S <: T.
Γ \- all(TX, S1, S2) <: all(_, T1, T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- abs(TX, K1, S2) <: abs(_, K1, T2) where maketop(K1, T1), [TX - bTVar(T1) | Γ] /- S2 <: T2.
lcst(Γ, S, T) :- simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T).
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (fn(TX :: T1) => M2) : all(TX, T1, T2) where [TX - bTVar(T1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, all(X, T11, T12)), Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _ where writeln(error : typeof(M)), !, halt.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' :: %w', [T]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S), !.
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x))![all('X', top, ('X' -> 'X'))])]).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]).
:- halt.

