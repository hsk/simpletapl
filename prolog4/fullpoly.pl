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
w(W) :- member(W, [bool, nat, unit, float, string, true, false, 0]).
x(X) :- \+ w(X), atom(X).
l(L) :- atom(L) ; integer(L).
t(T) :- T = bool ; T = nat ; T = unit ; T = float ; T = string ; T = X, x(X) ; T = (T1 -> T2), t(T1), t(T2) ; T = {Tf}, maplist([X : T1] >> (l(X), t(T1)), Tf) ; T = some(X, T1), x(X), t(T1) ; T = all(X, T1), x(X), t(T1).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = 0 ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1) ; M = unit ; M = F, float(F) ; M = M1 * M2, m(M1), m(M2) ; M = X, string(X) ; M = X, x(X) ; M = (fn(X : T1) -> M1), x(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = (let(X) = M1 in M2), x(X), m(M1), m(M2) ; M = fix(M1), m(M1) ; M = inert(T1), t(T1) ; M = M1 as T1, m(M1), t(T1) ; M = {Mf}, maplist([X = M1] >> (l(X), m(M1)), Mf) ; M = M1 # L, m(M1), l(L) ; M = M1 as T1, m(M1), t(T1) ; M = pack(T1, M1, T2), t(T1), m(M1), t(T2) ; M = unpack(TX, X, M1, M2), x(TX), x(X), m(M1), m(M2) ; M = (fn(TX) => M1), x(TX), m(M1) ; M = M1![T1], m(M1), t(T1).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
some(TX, T2)![(J -> S)] tsubst some(TX, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
all(TX, T2)![(J -> S)] tsubst all(TX, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_.
true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
unit![(J -> M)] subst unit.
F1![(J -> M)] subst F1 :- float(F1).
M1 * M2![(J -> M)] subst M1_ * M2_ :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
X![(J -> M)] subst X :- string(X).
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
fix(M1)![(J -> M)] subst fix(M1_) :- M1![(J -> M)] subst M1_.
inert(T1)![(J -> M)] subst inert(T1).
(M1 as T1)![(J -> M)] subst (M1_ as T1) :- M1![(J -> M)] subst M1_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
(M1 # L)![(J -> M)] subst (M1_ # L) :- M1![(J -> M)] subst M1_.
pack(T1, M2, T3)![(J -> M)] subst pack(T1, M2_, T3) :- M2![(J -> M)] subst M2_.
unpack(TX, X, M1, M2)![(J -> M)] subst unpack(TX, X, M1_, M2_) :- M1![X, (J -> M)] subst2 M1_, M2![X, (J -> M)] subst2 M2_.
(fn(TX) => M2)![(J -> M)] subst (fn(TX) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_, M3![(J -> S)] tmsubst M3_.
0![(J -> S)] tmsubst 0.
succ(M1)![(J -> S)] tmsubst succ(M1_) :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_) :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_) :- M1![(J -> S)] tmsubst M1_.
unit![(J -> M)] tmsubst unit.
F1![(J -> M)] tmsubst F1 :- float(F1).
M1 * M2![(J -> M)] tmsubst M1_ * M2_ :- M1![(J -> M)] tmsubst M1_, M2![(J -> M)] tmsubst M2_.
X![(J -> M)] tmsubst X :- string(X).
X![(J -> S)] tmsubst X :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(let(X) = M1 in M2)![(J -> S)] tmsubst (let(X) = M1_ in M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
fix(M1)![(J -> M)] tmsubst fix(M1_) :- M1![(J -> M)] tmsubst M1_.
inert(T1)![(J -> M)] tmsubst inert(T1).
(M1 as T1)![(J -> S)] tmsubst (M1_ as T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
{Mf}![(J -> M)] tmsubst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] tmsubst Mi_), Mf, Mf_).
(M1 # L)![(J -> M)] tmsubst (M1_ # L) :- M1![(J -> M)] tmsubst M1_.
pack(T1, M2, T3)![(J -> M)] tmsubst pack(T1_, M2_, T3_) :- T1![(J -> S)] tsubst T1_, M2![(J -> M)] tmsubst M2_, T3![(J -> S)] tsubst T3_.
unpack(TX, X, M1, M2)![(J -> M)] tmsubst unpack(TX, X, M1_, M2_) :- M1![TX, (J -> M)] tmsubst2 M1_, M2![TX, (J -> M)] tmsubst2 M2_.
(fn(TX) => M2)![(J -> S)] tmsubst (fn(TX) => M2_) :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))).
n(0).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
v(unit).
v(F1) :- float(F1).
v(X) :- string(X).
v((fn(_ : _) -> _)).
v({Mf}) :- maplist([L = M] >> v(M), Mf).
v(pack(_, V1, _)) :- v(V1).
v((fn(_) => _)).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_) where Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1 where n(N1).
Γ /- pred(M1) ==> pred(M1_) where Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false where n(N1).
Γ /- iszero(M1) ==> iszero(M1_) where Γ /- M1 ==> M1_.
Γ /- F1 * F2 ==> F3 where float(F1), float(F2), F3 is F1 * F2.
Γ /- V1 * M2 ==> V1 * M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 * M2 ==> M1_ * M2 where Γ /- M1 ==> M1_.
Γ /- X ==> M where x(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : _) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) where Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_ where M12![(X -> fix((fn(X : T) -> M12)))] subst M12_.
Γ /- fix(M1) ==> fix(M1_) where Γ /- M1 ==> M1_.
Γ /- V1 as _ ==> V1 where v(V1).
Γ /- M1 as T ==> M1_ as T where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M where member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L where Γ /- M1 ==> M1_.
Γ /- pack(T1, M2, T3) ==> pack(T1, M2_, T3) where Γ /- M2 ==> M2_.
Γ /- unpack(_, X, pack(T11, V12, _), M2) ==> M where v(V12), M2![(X -> V12)] subst M2_, M2_![(X -> T11)] tmsubst M.
Γ /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- (fn(X) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T)).
compute(Γ, X, T) :- x(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- X == T :- x(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- x(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- x(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- all(TX1, S2) == all(_, T2) :- [TX1 - bName | Γ] /- S2 = T2.
Γ /- some(TX1, S2) == some(_, T2) :- [TX1 - bName | Γ] /- S2 = T2.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- M1 * M2 : float where Γ /- M1 : T1, Γ /- T1 = float, Γ /- M2 : T2, Γ /- T2 = float.
Γ /- X : string where string(X).
Γ /- X : T where x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- (M1 # L) : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- pack(T1, M2, T) : T where simplify(Γ, T, some(Y, T2)), Γ /- M2 : S2, T2![(Y -> T1)] tsubst T2_, Γ /- S2 = T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, simplify(Γ, T1, some(_, T11)), [X - bVar(T11), TX - bTVar | Γ] /- M2 : T2.
Γ /- (fn(TX) => M2) : all(TX, T2) where [TX - bTVar | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, simplify(Γ, T1, all(X, T12)), T12![(X -> T2)] tsubst T12_.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar, '').
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, bMAbb(M, none)), Γ, [X - Bind | Γ]) :- Γ /- M : T, evalbinding(Γ, bMAbb(M, some(T)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S).
run(bind(X, bMAbb(M, some(T))), Γ, [X - Bind | Γ]) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, bMAbb(M, some(T)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S).
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(someBind(TX, X, M), Γ, [X - bMAbb(T12, some(TBody)), TX - bTVar | Γ]) :- Γ /- M : T, simplify(Γ, T, some(_, TBody)), Γ /- M ==>> pack(_, T12, _), writeln(TX), write(X), write(' : '), writeln(TBody).
run(someBind(TX, X, M), Γ, [X - bVar(TBody), TX - bTVar | Γ]) :- Γ /- M : T, simplify(Γ, T, some(_, TBody)), writeln(TX), write(X), write(' : '), writeln(TBody).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval((let(x) = true in x))]).
:- run([eval(2.0 * 3.14159)]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(0))]).
:- run([bind('T', bTAbb((nat -> nat))), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval((fn('X') => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X') => (fn(x : 'X') -> x))![all('X', ('X' -> 'X'))])]).
:- run([eval(pack(nat, (fn(x : nat) -> succ(x)), some('X', ('X' -> nat))))]).
:- run([eval(pack(all('Y', 'Y'), (fn(x : all('Y', 'Y')) -> x), some('X', ('X' -> 'X'))))]).
:- run([eval({[x = true, y = false]})]).
:- run([eval({[x = true, y = false]} # x)]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval({[1 = true, 2 = false]} # 1)]).
:- run([eval(pack(nat, {[c = 0, f = (fn(x : nat) -> succ(x))]}, some('X', {[c : 'X', f : ('X' -> nat)]})))]).
:- run([eval(unpack('X', ops, pack(nat, {[c = 0, f = (fn(x : nat) -> succ(x))]}, some('X', {[c : 'X', f : ('X' -> nat)]})), (ops # f) $ (ops # c)))]).
:- halt.

