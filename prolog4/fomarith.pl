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
val(X) :- X \= bool, X \= nat, X \= true, X \= false, X \= zero, atom(X).
k(K) :- K = '*' ; K = kArr(K1, K2), k(K1), k(K2).
t(T) :- T = bool ; T = nat ; T = X, val(X) ; T = (T1 -> T2), t(T1), t(T2) ; T = all(X, K, T1), val(X), k(K), t(T1) ; T = abs(TX, K, T2), val(TX), k(K), t(T2) ; T = T1 $ T2, t(T1), t(T2).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = zero ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1) ; M = X, val(X) ; M = (fn(X : T1) -> M1), val(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = let(X, M1, M2), val(X), m(M1), m(M2) ; M = as(M1, T1), m(M1), t(T1) ; M = (fn(TX :: K) => M2), val(TX), k(K), m(M2) ; M = M1![T2], m(M1), t(T2).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
J![(J -> S)] tsubst S :- val(J).
X![(J -> S)] tsubst X :- val(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
all(TX, K, T2)![(J -> S)] tsubst all(TX, K, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
abs(TX, K, T2)![(J -> S)] tsubst abs(TX, K, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![(J -> S)] tsubst T_ :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_.
true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
zero![(J -> M)] subst zero.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
J![(J -> M)] subst M :- val(J).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
let(X, M1, M2)![(J -> M)] subst let(X, M1_, M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
as(M1, T1)![(J -> M)] subst as(M1_, T1) :- M1![(J -> M)] subst M1_.
(fn(TX :: K) => M2)![(J -> M)] subst (fn(TX :: K) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
M1![(J -> M)] subst M1.
A![(J -> M)] subst B :- writeln(error : A![(J -> M)] subst B), fail.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_ :- T![(J -> M)] subst T_.
true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_, M3![(J -> S)] tmsubst M3_.
zero![(J -> S)] tmsubst zero.
succ(M1)![(J -> S)] tmsubst succ(M1_) :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_) :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_) :- M1![(J -> S)] tmsubst M1_.
X![(J -> S)] tmsubst X :- val(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
let(X, M1, M2)![(J -> S)] tmsubst let(X, M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
as(M1, T1)![(J -> S)] tmsubst as(M1_, T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
(fn(TX :: K) => M2)![(J -> S)] tmsubst (fn(TX :: K) => M2_) :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))).
n(zero).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
v((fn(_ : _) -> _)).
v((fn(_ :: _) => _)).
Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_) where Γ /- M1 ==> M1_.
Γ /- pred(zero) ==> zero.
Γ /- pred(succ(N1)) ==> N1 where n(N1).
Γ /- pred(M1) ==> pred(M1_) where Γ /- M1 ==> M1_.
Γ /- iszero(zero) ==> true.
Γ /- iszero(succ(N1)) ==> false where n(N1).
Γ /- iszero(M1) ==> iszero(M1_) where Γ /- M1 ==> M1_.
Γ /- X ==> M where val(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- let(X, V1, M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- let(X, M1, M2) ==> let(X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- as(V1, T) ==> V1 where v(V1).
Γ /- as(M1, T) ==> as(M1_, T) where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T) :- val(X), gettabb(Γ, X, T).
compute(Γ, abs(X, _, T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- X == T :- val(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- val(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- all(TX1, K1, S2) == all(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- abs(TX1, K1, S2) == abs(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !.
Γ \- X :: '*' where val(X), \+ member(X - _, Γ).
Γ \- X :: K where val(X), getb(Γ, X, bTVar(K)), !.
Γ \- X :: K where val(X), !, getb(Γ, X, bTAbb(_, some(K))).
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- all(TX, K1, T2) :: '*' where !, [TX - bTVar(K1) | Γ] /- T2 :: '*'.
Γ \- abs(TX, K1, T2) :: kArr(K1, K) where !, [TX - bTVar(K1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: kArr(K11, K12), Γ /- T2 :: K11.
Γ \- T :: '*'.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- zero : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- as(M1, T) : T where Γ /- T :: '*', Γ /- M1 : T1, Γ /- T1 = T.
Γ /- (fn(TX :: K1) => M2) : all(TX, K1, T2) where [TX - bTVar(K1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- T2 :: K2, Γ /- M1 : T1, simplify(Γ, T1, all(X, K2, T12)), T12![(X -> T2)] tsubst T12_.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(K1), R) :- swritef(R, ' :: %w', [K1]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T, none), R) :- Γ /- T :: K, swritef(R, ' :: %w', [K]).
show_bind(Γ, bTAbb(T, some(K)), R) :- swritef(R, ' :: %w', [K]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(bind(X, bMAbb(M, none)), Γ, [X - Bind | Γ]) :- Γ /- M : T, evalbinding(Γ, bMAbb(M, some(T)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S), !.
run(bind(X, bMAbb(M, some(T))), Γ, [X - Bind | Γ]) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, bMAbb(M, some(T)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S), !.
run(bind(X, bTAbb(T, none)), Γ, [X - Bind | Γ]) :- Γ /- T :: K, evalbinding(Γ, bTAbb(T, some(K)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S), !.
run(bind(X, bTAbb(T, some(K))), Γ, [X - Bind | Γ]) :- Γ /- T :: K, evalbinding(Γ, bTAbb(T, some(K)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S), !.
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S), !.
run(Ls) :- foldl(run, Ls, [], Γ).
:- run([eval((fn(x : bool) -> x)), eval((fn(x : bool) -> (fn(x : bool) -> x))), eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true))), bind(a, bVar(bool)), eval(a), eval((fn(x : bool) -> x) $ a), eval((fn(x : bool) -> (fn(x : bool) -> x) $ x) $ a), eval((fn(x : bool) -> x) $ true), eval((fn(x : bool) -> (fn(x : bool) -> x) $ x) $ true)]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval(let(x, true, x))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> x) $ zero)]).
:- run([eval((fn(x : nat) -> x) $ succ(zero))]).
:- run([eval((fn(x : nat) -> succ(x)) $ zero)]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(zero))]).
:- run([bind('T', bVar((nat -> nat)))]).
:- run([bind('T', bVar((nat -> nat))), eval((fn(f : (nat -> nat)) -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> f))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> f $ zero))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x))![all('X', '*', ('X' -> 'X'))])]).
:- run([bind('Pair', bTAbb(abs('X', '*', abs('Y', '*', all('R', '*', (('X' -> ('Y' -> 'R')) -> 'R')))), none)), bind(pair, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(x : 'X') -> (fn(y : 'Y') -> (fn('R' :: '*') => (fn(p : ('X' -> ('Y' -> 'R'))) -> p $ x $ y)))))), none)), bind(fst, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(p : 'Pair' $ 'X' $ 'Y') -> p!['X'] $ (fn(x : 'X') -> (fn(y : 'Y') -> x))))), none)), bind(snd, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(p : 'Pair' $ 'X' $ 'Y') -> p!['Y'] $ (fn(x : 'X') -> (fn(y : 'Y') -> y))))), none)), bind(pr, bMAbb(pair![nat]![bool] $ zero $ false, none)), eval(fst![nat]![bool] $ pr), eval(snd![nat]![bool] $ pr)]).
:- halt.

