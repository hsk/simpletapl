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
val(X) :- X \= bool, X \= nat, X \= unit, X \= float, X \= string, X \= true, X \= false, X \= zero, atom(X).
tsubst(J, S, bool, bool).
tsubst(J, S, nat, nat).
tsubst(J, S, unit, unit).
tsubst(J, S, float, float).
tsubst(J, S, string, string).
tsubst(J, S, J, S) :- val(J).
tsubst(J, S, X, X) :- val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_)) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, {Mf}, {Mf_}) :- maplist([L : T, L : T_] >> tsubst(J, S, T, T_), Mf, Mf_).
tsubst(J, S, ref(T1), ref(T1_)) :- tsubst(J, S, T1, T1_).
tsubst(J, S, all(TX, K1, T2), all(TX, K1, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, some(TX, K1, T2), some(TX, K1, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, abs(TX, K1, T2), abs(TX, K1, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, app(TX, T1, T2), app(TX, T1_, T2_)) :- tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst2(X, X, S, T, T).
tsubst2(X, J, S, T, T_) :- tsubst(J, S, T, T_).
subst(J, M, true, true).
subst(J, M, false, false).
subst(J, M, if(M1, M2, M3), if(M1_, M2_, M3_)) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_), subst(J, M, M3, M3_).
subst(J, M, zero, zero).
subst(J, M, succ(M1), succ(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, pred(M1), pred(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, iszero(M1), iszero(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, unit, unit).
subst(J, M, F1, F1) :- float(F1).
subst(J, M, timesfloat(M1, M2), timesfloat(M1_, M2_)) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, X, X) :- string(X).
subst(J, M, J, M) :- val(J).
subst(J, M, X, X) :- val(X).
subst(J, M, (fn(X : T1) -> M2), (fn(X : T1) -> M2_)) :- subst2(X, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, let(X, M1, M2), let(X, M1_, M2_)) :- subst(J, M, M1, M1_), subst2(X, J, M, M2, M2_).
subst(J, M, fix(M1), fix(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, inert(T1), inert(T1)).
subst(J, M, as(M1, T1), as(M1_, T1)) :- subst(J, M, M1, M1_).
subst(J, M, {Mf}, {Mf_}) :- maplist([L = Mi, L = Mi_] >> subst(J, M, Mi, Mi_), Mf, Mf_).
subst(J, M, proj(M1, L), proj(M1_, L)) :- subst(J, M, M1, M1_).
subst(J, M, ref(M1), ref(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, deref(M1), deref(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, assign(M1, M2), assign(M1_, M2_)) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, loc(L), loc(L)).
subst(J, M, (fn(TX :: K1) => M2), (fn(TX :: K1) => M2_)) :- subst(J, M, M2, M2_).
subst(J, M, M1![T2], M1_![T2]) :- subst(J, M, M1, M1_).
subst(J, M, pack(T1, M2, T3), pack(T1, M2_, T3)) :- subst(J, M, M2, M2_).
subst(J, M, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) :- subst2(X, J, M, M1, M1_), subst2(X, J, M, M2, M2_).
subst(J, M, S, _) :- writeln(error : subst(J, M, S)), fail.
subst2(J, J, M, S, S).
subst2(X, J, M, S, M_) :- subst(J, M, S, M_).
tmsubst(J, S, true, true).
tmsubst(J, S, false, false).
tmsubst(J, S, if(M1, M2, M3), if(M1_, M2_, M3_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_), tmsubst(J, S, M3, M3_).
tmsubst(J, S, zero, zero).
tmsubst(J, S, succ(M1), succ(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, pred(M1), pred(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, iszero(M1), iszero(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, unit, unit).
tmsubst(J, S, F1, F1) :- float(F1).
tmsubst(J, S, timesfloat(M1, M2), timesfloat(M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, X, X) :- string(X).
tmsubst(J, S, X, X) :- val(X).
tmsubst(J, S, (fn(X : T1) -> M2), (fn(X : T1_) -> M2_)) :- tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, M1 $ M2, M1_ $ M2_) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, let(X, M1, M2), let(X, M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, fix(M1), fix(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, inert(T1), inert(T1)).
tmsubst(J, S, as(M1, T1), as(M1_, T1_)) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T1, T1_).
tmsubst(J, S, {Mf}, {Mf_}) :- maplist([L = Mi, L = Mi_] >> tmsubst(J, S, Mi, Mi_), Mf, Mf_).
tmsubst(J, S, proj(M1, L), proj(M1_, L)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, ref(M1), ref(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, deref(M1), deref(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, assign(M1, M2), assign(M1_, M2_)) :- tmsubst(J, S, M2, M2_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, loc(L), loc(L)).
tmsubst(J, S, (fn(TX :: K1) => M2), (fn(TX :: K1) => M2_)) :- tmsubst2(TX, J, S, M2, M2_).
tmsubst(J, S, M1![T2], M1_![T2_]) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T2, T2_).
tmsubst(J, S, pack(T1, M2, T3), pack(T1_, M2_, T3_)) :- tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_), tsubst(J, S, T3, T3_).
tmsubst(J, S, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst2(X, X, S, T, T).
tmsubst2(X, J, S, T, T_) :- tmsubst(J, S, T, T_).
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))).
n(zero).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
v(unit).
v(F1) :- float(F1).
v(X) :- string(X).
v((fn(_ : _) -> _)).
v({Mf}) :- maplist([L = M] >> v(M), Mf).
v(loc(_)).
v(pack(_, V1, _)) :- v(V1).
v((fn(_ :: _) => _)).
extendstore(St, V1, Len, St_) :- length(St, Len), append(St, [V1], St_).
lookuploc(St, L, R) :- nth0(L, St, R).
updatestore([_ | St], 0, V1, [V1 | St]).
updatestore([V | St], N1, V1, [V | St_]) :- N is N1 - 1, updatestore(St, N, V1, St_).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ / St /- if(true, M2, M3) ==> M2 / St.
Γ / St /- if(false, M2, M3) ==> M3 / St.
Γ / St /- if(M1, M2, M3) ==> if(M1_, M2, M3) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- succ(M1) ==> succ(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- pred(zero) ==> zero / St.
Γ / St /- pred(succ(NV1)) ==> NV1 / St where n(NV1).
Γ / St /- pred(M1) ==> pred(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- iszero(zero) ==> true / St.
Γ / St /- iszero(succ(NV1)) ==> false / St where n(NV1).
Γ / St /- iszero(M1) ==> iszero(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- timesfloat(F1, F2) ==> F3 / St where float(F1), float(F2), F3 is F1 * F2.
Γ / St /- timesfloat(F1, M2) ==> timesfloat(F1, M2_) / St_ where float(F1), eval1(Γ, St, M2, M2_).
Γ / St /- timesfloat(M1, M2) ==> timesfloat(M1_, M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- X ==> M / St where val(X), getb(Γ, X, bMAbb(M, _)).
Γ / St /- (fn(X : _) -> M12) $ V2 ==> R / St where v(V2), subst(X, V2, M12, R).
Γ / St /- V1 $ M2 ==> (V1 $ M2_) / St_ where v(V1), Γ / St /- M2 ==> M2_ / St_.
Γ / St /- M1 $ M2 ==> (M1_ $ M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- let(X, V1, M2) ==> M2_ / St where v(V1), subst(X, V1, M2, M2_).
Γ / St /- let(X, M1, M2) ==> let(X, M1_, M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- fix((fn(X : T11) -> M12)) ==> M / St where subst(X, fix((fn(X : T11) -> M12)), M12, M).
Γ / St /- fix(M1) ==> fix(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- as(V1, _) ==> V1 / St where v(V1).
Γ / St /- as(M1, T) ==> as(M1_, T) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- {Mf} ==> {Mf_} / St_ where e(Mf, M, Mf_, M_), Γ / St /- M ==> M_ / St_.
Γ / St /- proj({Mf}, L) ==> M / St where member(L = M, Mf).
Γ / St /- proj(M1, L) ==> proj(M1_, L) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- ref(M1) ==> ref(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- deref(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- deref(M1) ==> deref(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- assign(loc(L), V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- assign(V1, M2) ==> assign(V1, M2_) / St_ where v(V1), Γ / St /- M2 ==> M2_ / St_.
Γ / St /- assign(M1, M2) ==> assign(M1_, M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- (fn(X :: K) => M11)![T2] ==> M11_ / St_ where tmsubst(X, T2, M11, M11_).
Γ / St /- M1![T2] ==> (M1_![T2]) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- pack(T1, M2, T3) ==> pack(T1, M2_, T3) / St_ where Γ / St /- M2 ==> M2_ / St_.
Γ / St /- unpack(_, X, pack(T11, V12, _), M2) ==> M / St where v(V12), subst(X, V12, M2, M2_), tmsubst(X, T11, M2_, M).
Γ / St /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) / St_ where St / Γ /- M1 ==> M1_ / St_.
Γ / St /- M ==>> M_ / St_ where Γ / St /- M ==> M1 / St1, Γ / St1 /- M1 ==>> M_ / St_.
Γ / St /- M ==>> M / St.
evalbinding(Γ, St, bMAbb(M, T), bMAbb(M_, T), St_) :- Γ / St /- M ==>> M_ / St_.
evalbinding(Γ, St, Bind, Bind, St).
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T) :- val(X), gettabb(Γ, X, T).
compute(Γ, abs(X, _, T12) $ T2, T) :- tsubst(X, T2, T12, T).
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- X == T :- val(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- val(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- ref(S) == ref(T) :- Γ /- S = T.
Γ /- all(TX1, K1, S2) == all(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- some(TX1, K1, S2) == some(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- abs(TX1, K1, S2) == abs(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ \- T :: K where Γ /- T :: K, !.
Γ \- T :: K where writeln(error : kindof(T, K)), fail.
Γ /- X :: '*' where val(X), \+ member(X - _, Γ).
Γ /- X :: K where val(X), getb(Γ, X, bTVar(K)), !.
Γ /- X :: K where val(X), !, getb(Γ, X, bTAbb(_, some(K))).
Γ /- (T1 -> T2) :: '*' where !, Γ \- T1 :: '*', Γ \- T2 :: '*'.
Γ /- {Tf} :: '*' where maplist([L : S] >> (Γ \- S :: '*'), Tf).
Γ /- all(TX, K1, T2) :: '*' where !, [TX - bTVar(K1) | Γ] \- T2 :: '*'.
Γ /- some(TX, K1, T2) :: '*' where !, [TX - bTVar(K1) | Γ] \- T2 :: '*'.
Γ /- abs(TX, K1, T2) :: kArr(K1, K) where !, [TX - bTVar(K1) | Γ] \- T2 :: K.
Γ /- T1 $ T2 :: K12 where !, Γ \- T1 :: kArr(K11, K12), Γ \- T2 :: K11.
Γ /- T :: '*'.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- zero : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- timesfloat(M1, M2) : float where Γ /- M1 : T1, Γ /- T1 = float, Γ /- M2 : T2, Γ /- T2 = float.
Γ /- X : string where string(X).
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ \- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- as(M1, T) : T where Γ \- T :: '*', Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- proj(M1, L) : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- deref(M1) : T1 where Γ /- M1 : T, simplify(Γ, T, ref(T1)).
Γ /- assign(M1, M2) : unit where Γ /- M1 : T, simplify(Γ, T, ref(T1)), Γ /- M2 : T2, Γ /- T2 = T1.
Γ /- pack(T1, M2, T) : T where Γ \- T :: '*', simplify(Γ, T, some(Y, K1, T2)), Γ \- T1 :: K1, Γ /- M2 : S2, tsubst(Y, T1, T2, T2_), Γ /- S2 = T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, simplify(Γ, T1, some(_, K, T11)), [X - bVar(T11), TX - bTVar(K) | Γ] /- M2 : T2.
Γ /- (fn(TX :: K1) => M2) : all(TX, K1, T2) where [TX - bTVar(K1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ \- T2 :: K2, Γ /- M1 : T1, simplify(Γ, T1, all(X, K2, T12)), tsubst(X, T2, T12, T12_).
Γ /- M : _ where writeln(error : typeof(M)), !, halt.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(K1), R) :- swritef(R, ' :: %w', [K1]).
show_bind(Γ, bTAbb(T, none), R) :- Γ \- T :: K, swritef(R, ' :: %w', [K]).
show_bind(Γ, bTAbb(T, some(K)), R) :- swritef(R, ' :: %w', [K]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
run(eval(M), (Γ, St), (Γ, St_)) :- !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
run(bind(X, Bind), (Γ, St), ([X - Bind_ | Γ], St_)) :- check_bind(Γ, Bind, Bind1), evalbinding(Γ, St, Bind1, Bind_, St_), write(X), show_bind(Γ, Bind_, R), writeln(R).
run(someBind(TX, X, M), (Γ, St), ([X - B, TX - bTVar(K) | Γ], St_)) :- !, Γ /- M : T, simplify(Γ, T, some(_, K, TBody)), Γ / St /- M ==>> M_ / St_, check_someBind(TBody, M_, B), writeln(TX), write(X), write(' : '), writeln(TBody).
check_bind(Γ, bName, bName).
check_bind(Γ, bTVar(K), bTVar(K)).
check_bind(Γ, bTAbb(T, none), bTAbb(T, some(K))) :- Γ \- T :: K.
check_bind(Γ, bTAbb(T, some(K)), bTAbb(T, some(K))) :- Γ \- T :: K.
check_bind(Γ, bVar(T), bVar(T)).
check_bind(Γ, bMAbb(M, none), bMAbb(M, some(T))) :- Γ /- M : T.
check_bind(Γ, bMAbb(M, some(T)), bMAbb(M, some(T))) :- Γ /- M : T1, Γ /- T1 = T.
check_someBind(TBody, pack(_, T12, _), bMAbb(T12, some(TBody))).
check_someBind(TBody, _, bVar(TBody)).
run(Ls) :- foldl(run, Ls, ([], []), _).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval(let(x, true, x))]).
:- run([eval(timesfloat(2.0, 3.14159))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(zero))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x))![all('X', '*', ('X' -> 'X'))])]).
:- run([eval(pack(all('Y', '*', 'Y'), (fn(x : all('Y', '*', 'Y')) -> x), some('X', '*', ('X' -> 'X'))))]).
:- run([eval({[x = true, y = false]})]).
:- run([eval(proj({[x = true, y = false]}, x))]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval(proj({[1 = true, 2 = false]}, 1))]).
:- run([eval(pack(nat, {[c = zero, f = (fn(x : nat) -> succ(x))]}, some('X', '*', {[c : 'X', f : ('X' -> nat)]})))]).
:- run([eval(unpack('X', ops, pack(nat, {[c = zero, f = (fn(x : nat) -> succ(x))]}, some('X', '*', {[c : 'X', f : ('X' -> nat)]})), proj(ops, f) $ proj(ops, c)))]).
:- run([bind('Pair', bTAbb(abs('X', '*', abs('Y', '*', all('R', '*', (('X' -> ('Y' -> 'R')) -> 'R')))), none)), bind(pair, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(x : 'X') -> (fn(y : 'Y') -> (fn('R' :: '*') => (fn(p : ('X' -> ('Y' -> 'R'))) -> p $ x $ y)))))), none)), bind(fst, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(p : 'Pair' $ 'X' $ 'Y') -> p!['X'] $ (fn(x : 'X') -> (fn(y : 'Y') -> x))))), none)), bind(snd, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(p : 'Pair' $ 'X' $ 'Y') -> p!['Y'] $ (fn(x : 'X') -> (fn(y : 'Y') -> y))))), none)), bind(pr, bMAbb(pair![nat]![bool] $ zero $ false, none)), eval(fst![nat]![bool] $ pr), eval(snd![nat]![bool] $ pr)]).
:- halt.

