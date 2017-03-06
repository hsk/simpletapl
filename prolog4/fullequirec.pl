:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::', '#', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
term_expansion((A where B), (A :- B)).
:- style_check(- singleton).
val(X) :- X \= bool, X \= nat, X \= unit, X \= unit, X \= float, X \= string, atom(X).
l(L) :- atom(L) ; integer(L).
t(T) :- T = bool ; T = nat ; T = unit ; T = float ; T = string ; T = X, val(X) ; T = (T1 -> T2), t(T1), t(T2) ; T = {Tf}, maplist([X : T1] >> (l(X), t(T1)), Tf) ; T = variant(Tf), maplist([X : T1] >> (val(X), t(T1)), Tf) ; T = rec(X, T1), val(X), t(T1).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = 0 ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1) ; M = unit ; M = F, float(F) ; M = M1 * M2, m(M1), m(M2) ; M = X, string(X) ; M = X, val(X) ; M = (fn(X : T1) -> M1), val(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = let(X, M1, M2), val(X), m(M1), m(M2) ; M = fix(M1), m(M1) ; M = inert(T1), t(T1) ; M = M1 as T1, m(M1), t(T1) ; M = {Tf}, maplist([X = M1] >> (l(X), m(M1)), Mf) ; M = M1 # L, m(M1), l(L) ; M = case(M1, Cases), m(M1), maplist([X = (X1, M2)] >> (val(X), (val(X1), m(M2))), Cases) ; M = tag(X, M1, T1), val(X), m(M1), t(T1).
maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
J![(J -> S)] tsubst S :- val(J).
X![(J -> S)] tsubst X :- val(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
variant(Mf)![(J -> S)] tsubst variant(Mf_) :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
rec(X, T1)![(J -> S)] tsubst rec(X, T1_) :- T1![X, (J -> S)] tsubst2 T1_.
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
J![(J -> M)] subst M :- val(J).
X![(J -> M)] subst X :- val(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
let(X, M1, M2)![(J -> M)] subst let(X, M1_, M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
fix(M1)![(J -> M)] subst fix(M1_) :- M1![(J -> M)] subst M1_.
inert(T1)![(J -> M)] subst inert(T1).
(M1 as T1)![(J -> M)] subst (M1_ as T1) :- M1![(J -> M)] subst M1_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
(M1 # L)![(J -> M)] subst (M1_ # L) :- M1![(J -> M)] subst M1_.
tag(L, M1, T1)![(J -> M)] subst tag(L, M1_, T1) :- M1![(J -> M)] subst M1_.
case(M, Cases)![(J -> M)] subst case(M_, Cases_) :- M1![(J -> M)] subst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> M)] subst M1_), Cases, Cases_).
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
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
v(tag(_, M1, _)) :- v(M1).
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
Γ /- X ==> M where val(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : _) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- let(X, V1, M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- let(X, M1, M2) ==> let(X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_ where M12![(X -> fix((fn(X : T) -> M12)))] subst M12_.
Γ /- fix(M1) ==> fix(M1_) where Γ /- M1 ==> M1_.
Γ /- V1 as _ ==> V1 where v(V1).
Γ /- M1 as T ==> M1_ as T where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M where member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L where Γ /- M1 ==> M1_.
Γ /- tag(L, M1, T) ==> tag(L, M1_, T) where Γ /- M1 ==> M1_.
Γ /- case(tag(L, V11, _), Bs) ==> M_ where v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ /- case(M1, Bs) ==> case(M1_, Bs) where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T)).
compute(Γ, rec(X, S1), T) :- S1![(X -> rec(X, S1))] tsubst T.
compute(Γ, X, T) :- val(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T :- teq([], Γ, S, T).
teq(Seen, Γ, S, T) :- member((S, T), Seen).
teq(Seen, Γ, bool, bool).
teq(Seen, Γ, nat, nat).
teq(Seen, Γ, unit, unit).
teq(Seen, Γ, float, float).
teq(Seen, Γ, string, string).
teq(Seen, Γ, rec(X, S1), T) :- S = rec(X, S1), S1![(X -> S)] tsubst S1_, teq([(S, T) | Seen], Γ, S1_, T).
teq(Seen, Γ, S, rec(X, T1)) :- T = rec(X, T1), T1![(X -> T)] tsubst T1_, teq([(S, T) | Seen], Γ, S, T1_).
teq(Seen, Γ, X, X) :- val(X).
teq(Seen, Γ, X, T) :- val(X), gettabb(Γ, X, S), teq(Seen, Γ, S, T).
teq(Seen, Γ, S, X) :- val(X), gettabb(Γ, X, T), teq(Seen, Γ, S, T).
teq(Seen, Γ, (S1 -> S2), (T1 -> T2)) :- teq(Seen, Γ, S1, T1), teq(Seen, Γ, S2, T2).
teq(Seen, Γ, {Sf}, {Tf}) :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), teq(Seen, Γ, S, T)), Tf).
teq(Seen, Γ, variant(Sf), variant(Tf)) :- length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> teq(Seen, Γ, S, T), Sf, Tf).
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
Γ /- X : T where val(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- (M1 # L) : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- tag(Li, Mi, T) : T where simplify(Γ, T, variant(Tf)), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ = Te.
Γ /- case(M, Cases) : T1 where Γ /- M : T, simplify(Γ, T, variant(Tf)), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, [T1 | RestT]), maplist([Tt] >> (Γ /- Tt = T1), RestT).
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar, '').
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, bMAbb(M, none)), Γ, [X - Bind | Γ]) :- Γ /- M : T, evalbinding(Γ, bMAbb(M, some(T)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S), !.
run(bind(X, bMAbb(M, some(T))), Γ, [X - Bind | Γ]) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, bMAbb(M, some(T)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S), !.
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S), !.
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval("hello")]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval(2.0 * 3.14159)]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(0))]).
:- run([bind('T', bTAbb((nat -> nat))), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval((fn(f : rec('X', ('A' -> 'A'))) -> (fn(x : 'A') -> f $ x)))]).
:- run([eval({[x = true, y = false]})]).
:- run([eval({[x = true, y = false]} # x)]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval({[1 = true, 2 = false]} # 1)]).
:- run([eval((fn(x : variant([a : bool, b : bool])) -> x))]).
:- run([bind('Counter', bTAbb(rec('P', {[get : nat, inc : (unit -> 'P')]}))), bind(p, bMAbb(let(create, fix((fn(cr : ({[x : nat]} -> 'Counter')) -> (fn(s : {[x : nat]}) -> {[get = s # x, inc = (fn('_' : unit) -> cr $ {[x = succ(s # x)]})]}))), create $ {[x = 0]}), none)), eval(p # get), bind(p, bMAbb((p # inc) $ unit, none)), eval(p # get), bind(p, bMAbb((p # inc) $ unit, none)), eval(p # get), bind(get, bMAbb((fn(p : 'Counter') -> p # get), none)), bind(inc, bMAbb((fn(p : 'Counter') -> p # inc), none)), eval(get $ p), bind(p, bMAbb(inc $ p $ unit, none)), eval(get $ p)]).
:- run([eval(let(x, true, x))]).
:- run([eval(unit)]).
:- halt.

