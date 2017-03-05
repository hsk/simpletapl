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
val(X) :- X \= bool, X \= nat, X \= unit, X \= float, X \= string, X \= top, X \= bot, X \= true, X \= false, X \= zero, X \= error, atom(X).
maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).
tsubst(J, S, bool, bool).
tsubst(J, S, nat, nat).
tsubst(J, S, unit, unit).
tsubst(J, S, float, float).
tsubst(J, S, string, string).
tsubst(J, S, top, top).
tsubst(J, S, bot, bot).
tsubst(J, S, J, S) :- val(J).
tsubst(J, S, X, X) :- val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_)) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, {Mf}, {Mf_}) :- maplist([L : T, L : T_] >> tsubst(J, S, T, T_), Mf, Mf_).
tsubst(J, S, variant(Mf), variant(Mf_)) :- maplist([L : T, L : T_] >> tsubst(J, S, T, T_), Mf, Mf_).
tsubst(J, S, ref(T1), ref(T1_)) :- tsubst(J, S, T1, T1_).
tsubst(J, S, source(T1), source(T1_)) :- tsubst(J, S, T1, T1_).
tsubst(J, S, sink(T1), sink(T1_)) :- tsubst(J, S, T1, T1_).
tsubst(J, S, all(TX, T1, T2), all(TX, T1_, T2_)) :- tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, T, T_) :- writeln(error : tsubst(J, S, T, T_)), halt.
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
subst(J, M, tag(L, M1, T1), tag(L, M1_, T1)) :- subst(J, M, M1, M1_).
subst(J, M, case(M1, Cases), case(M1_, Cases_)) :- subst(J, M, M1, M1_), maplist([L = (X, M1), L = (X, M1_)] >> subst(J, M, M1, M1_), Cases, Cases_).
subst(J, M, ref(M1), ref(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, deref(M1), deref(M1_)) :- subst(J, M, M1, M1_).
subst(J, M, assign(M1, M2), assign(M1_, M2_)) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, loc(L), loc(L)).
subst(J, M, try(M1, M2), try(M1_, M2_)) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, error, error).
subst(J, M, (fn(TX :: T1) => M2), (fn(TX :: T1) => M2_)) :- subst(J, M, M2, M2_).
subst(J, M, M1![T2], M1_![T2]) :- subst(J, M, M1, M1_).
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
tmsubst(J, S, tag(L, M1, T1), tag(L, M1_, T1_)) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T1, T1_).
tmsubst(J, S, case(M1, Cases), case(M1_, Cases_)) :- tmsubst(J, S, M1, M1_), maplist([L = (X, M1), L = (X, M1_)] >> subst(J, S, M1, M1_), Cases, Cases_).
tmsubst(J, S, ref(M1), ref(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, deref(M1), deref(M1_)) :- tmsubst(J, S, M1, M1_).
tmsubst(J, S, assign(M1, M2), assign(M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, loc(L), loc(L)).
tmsubst(J, S, try(M1, M2), try(M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, error, error).
tmsubst(J, S, (fn(TX :: T1) => M2), (fn(TX :: T1_) => M2_)) :- tsubst2(TX, J, S, T1, T1_), tmsubst2(TX, J, S, M2, M2_).
tmsubst(J, S, M1![T2], M1_![T2_]) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T2, T2_).
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
v(tag(_, M1, _)) :- v(M1).
v(loc(_)).
v((fn(_ :: _) => _)).
extendstore(St, V1, Len, St_) :- length(St, Len), append(St, [V1], St_).
lookuploc(St, L, R) :- nth0(L, St, R).
updatestore([_ | St], 0, V1, [V1 | St]).
updatestore([V | St], N1, V1, [V | St_]) :- N is N1 - 1, updatestore(St, N, V1, St_).
eval_context(if(M1, M2, M3), ME, if(MH, M2, M3), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(succ(M1), ME, succ(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(pred(M1), ME, pred(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(iszero(M1), ME, iszero(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(timesfloat(M1, M2), ME, timesfloat(MH, M2), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(timesfloat(V1, M2), ME, timesfloat(V1, MH), H) :- \+ v(M2), eval_context(M1, ME, MH, H).
eval_context(M1 $ M2, ME, MH $ M2, H) :- \+ v(M1) -> eval_context(M1, ME, MH, H).
eval_context(V1 $ M2, ME, V1 $ MH, H) :- \+ v(M2) -> eval_context(M2, ME, MH, H).
eval_context(let(X, M1, M2), ME, let(X, MH, M2), H) :- \+ v(M1) -> eval_context(M1, ME, MH, H).
eval_context(fix(M1), ME, fix(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(as(M1, T), ME, as(MH, T), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(proj(M1, L), ME, proj(MH, L), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(tag(L, M1, T), ME, tag(L, MH, T), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(case(M1, Branches), ME, case(MH, Branches), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(ref(M1), ME, ref(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(deref(M1), ME, deref(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(assign(M1, M2), ME, assign(MH, M2), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(assign(V1, M2), ME, assign(V1, MH), H) :- \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(M1![T], ME, MH![T], H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context({Mf}, ME, {MH}, H) :- \+ v(M1), e(Mf, ME, MH, H).
eval_context(try(M1, M2), M1, try(H, M2), H).
eval_context(M1, M1, H, H) :- \+ v(M1).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ / St /- if(true, M2, M3) ==> M2 / St.
Γ / St /- if(false, M2, M3) ==> M3 / St.
Γ / St /- pred(zero) ==> zero / St.
Γ / St /- pred(succ(NV1)) ==> NV1 / St where n(NV1).
Γ / St /- iszero(zero) ==> true / St.
Γ / St /- iszero(succ(NV1)) ==> false / St where n(NV1).
Γ / St /- timesfloat(F1, F2) ==> F3 / St where float(F1), float(F2), F3 is F1 * F2.
Γ / St /- X ==> M / St where val(X), getb(Γ, X, bMAbb(M, _)).
Γ / St /- (fn(X : _) -> M12) $ V2 ==> R / St where v(V2), subst(X, V2, M12, R).
Γ / St /- let(X, V1, M2) ==> M2_ / St where v(V1), subst(X, V1, M2, M2_).
Γ / St /- fix((fn(X : T11) -> M12)) ==> M / St where subst(X, fix((fn(X : T11) -> M12)), M12, M).
Γ / St /- as(V1, _) ==> V1 / St where v(V1).
Γ / St /- proj({Mf}, L) ==> M / St where member(L = M, Mf).
Γ / St /- case(tag(L, V11, _), Bs) ==> M_ / St where v(V11), member(L = (X, M), Bs), subst(X, V11, M, M_).
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- deref(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- assign(loc(L), V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- (fn(X) => M11)![T2] ==> M11_ / St_ where tmsubst(X, T2, M11, M11_).
Γ / St /- try(error, M2) ==> M2 / St.
Γ / St /- try(V1, M2) ==> V1 / St where v(V1).
Γ / St /- try(M1, M2) ==> try(M1_, M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- error ==> _ / _ where !, fail.
Γ / St /- M ==> error / St where eval_context(M, error, _, _), !.
Γ / St /- M ==> error / St where eval_context(M, M, _, _), !, fail.
Γ / St /- M ==> M_ / St_ where eval_context(M, ME, M_, H), Γ / St /- ME ==> H / St_.
Γ / St /- M ==>> M_ / St_ where Γ / St /- M ==> M1 / St1, Γ / St1 /- M1 ==>> M_ / St_.
Γ / St /- M ==>> M / St.
evalbinding(Γ, St, bMAbb(M, T), bMAbb(M_, T), St_) :- Γ / St /- M ==>> M_ / St_.
evalbinding(Γ, St, Bind, Bind, St).
promote(Γ, X, T) :- val(X), getb(Γ, X, bTVar(T)).
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T)).
compute(Γ, X, T) :- val(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- top == top.
Γ /- bot == bot.
Γ /- X == T :- val(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- val(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- variant(Sf) == variant(Tf) :- length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf).
Γ /- ref(S) == ref(T) :- Γ /- S = T.
Γ /- source(S) == source(T) :- Γ /- S = T.
Γ /- sink(S) == sink(T) :- Γ /- S = T.
Γ /- all(TX, S1, S2) == all(_, T1, T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ \- S <: T where Γ /- S = T.
Γ \- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ <: T_.
Γ /- _ <: top.
Γ /- bot <: _.
Γ /- X <: T where val(X), promote(Γ, X, S), Γ \- S <: T.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ \- T1 <: S1, Γ \- S2 <: T2.
Γ /- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ \- S <: T), TF).
Γ /- variant(SF) <: variant(TF) where maplist([L : S] >> (member(L : T, TF), Γ \- S <: T), SF).
Γ /- ref(S) <: ref(T) where Γ \- S <: T, Γ \- T <: S.
Γ /- ref(S) <: source(T) where Γ \- S <: T.
Γ /- source(S) <: source(T) where Γ \- S <: T.
Γ /- ref(S) <: sink(T) where Γ \- T <: S.
Γ /- sink(S) <: sink(T) where Γ \- T <: S.
Γ /- all(TX, S1, S2) <: all(_, T1, T2) where Γ \- S1 <: T1, Γ \- T1 <: S1, [TX - bTVar(T1) | Γ] \- S2 <: T2.
join(Γ, S, T, T) :- Γ \- S <: T.
join(Γ, S, T, S) :- Γ \- T <: S.
join(Γ, S, T, R) :- simplify(Γ, S, S_), simplify(Γ, T, T_), join2(Γ, S_, T_, R).
join2(Γ, {SF}, {TF}, {UF_}) :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : S, L : T_] >> (member(L : T, TF), join(Γ, S, T, T_)), UF, UF_).
join2(Γ, all(TX, S1, S2), all(_, T1, T2), all(TX, S1, T2_)) :- Γ \- S1 <: T1, Γ \- T1 <: S1, join([TX - bTVar(T1) | Γ], T1, T2, T2_).
join2(Γ, all(TX, S1, S2), all(_, T1, T2), top).
join2(Γ, (S1 -> S2), (T1 -> T2), (S_ -> T_)) :- meet(Γ, S1, T1, S_), join(Γ, S2, T2, T_).
join2(Γ, ref(S), ref(T), ref(S)) :- Γ \- S <: T, Γ \- T <: S.
join2(Γ, ref(S), ref(T), source(T_)) :- join(Γ, S, T, T_).
join2(Γ, source(S), source(T), source(T_)) :- join(Γ, S, T, T_).
join2(Γ, ref(S), source(T), source(T_)) :- join(Γ, S, T, T_).
join2(Γ, source(S), ref(T), source(T_)) :- join(Γ, S, T, T_).
join2(Γ, sink(S), sink(T), sink(T_)) :- meet(Γ, S, T, T_).
join2(Γ, ref(S), sink(T), sink(T_)) :- meet(Γ, S, T, T_).
join2(Γ, sink(S), ref(T), sink(T_)) :- meet(Γ, S, T, T_).
join2(Γ, _, _, top).
meet(Γ, S, T, S) :- Γ \- S <: T.
meet(Γ, S, T, T) :- Γ \- T <: S.
meet(Γ, S, T, R) :- simplify(Γ, S, S_), simplify(Γ, T, T_), meet2(Γ, S_, T_, R).
meet2(Γ, {SF}, {TF}, {UF_}) :- maplist([L : S, L : T_] >> (member(L : T, TF), meet(Γ, S, T, T_) ; T_ = S), SF, SF_), include([L : _] >> (\+ member(L : _, SF)), TF, TF_), append(SF_, TF_, UF_).
meet2(Γ, all(TX, S1, S2), all(_, T1, T2), all(TX, S1, T2_)) :- Γ \- S1 <: T1, Γ \- T1 <: S1, meet([TX - bTVar(T1) | Γ], T1, T2, T2_).
meet2(Γ, (S1 -> S2), (T1 -> T2), (S_ -> T_)) :- join(Γ, S1, T1, S_), meet(Γ, S2, T2, T_).
meet2(Γ, ref(S), ref(T), ref(T)) :- Γ \- S <: T, Γ \- T <: S.
meet2(Γ, ref(S), ref(T), source(T_)) :- meet(Γ, S, T, T_).
meet2(Γ, source(S), source(T), source(T_)) :- meet(Γ, S, T, T_).
meet2(Γ, ref(S), source(T), source(T_)) :- meet(Γ, S, T, T_).
meet2(Γ, source(S), ref(T), source(T_)) :- meet(Γ, S, T, T_).
meet2(Γ, sink(S), sink(T), sink(T_)) :- join(Γ, S, T, T_).
meet2(Γ, ref(S), sink(T), sink(T_)) :- join(Γ, S, T, T_).
meet2(Γ, sink(S), ref(T), sink(T_)) :- join(Γ, S, T, T_).
meet2(_, _, bot).
lcst(Γ, S, T) :- simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T).
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T where Γ /- M1 : T1, Γ \- T1 <: bool, Γ /- M2 : T2, Γ /- M3 : T3, join(Γ, T2, T3, T).
Γ /- zero : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ \- T1 <: nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ \- T1 <: nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ \- T1 <: nat.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- timesfloat(M1, M2) : float where Γ /- M1 : T1, Γ \- T1 <: float, Γ /- M2 : T2, Γ \- T2 <: float.
Γ /- X : string where string(X).
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : bot where Γ /- M1 : T1, Γ /- M2 : T2, lcst(Γ, T1, bot).
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ \- T2 <: T11.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ \- T12 <: T11.
Γ /- fix(M1) : bot where Γ /- M1 : T1, lcst(Γ, T1, bot).
Γ /- inert(T) : T.
Γ /- as(M1, T) : T where Γ /- M1 : T1, Γ \- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- proj(M1, L) : T where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- proj(M1, L) : bot where Γ /- M1 : T1, lcst(Γ, T1, bot).
Γ /- tag(Li, Mi, T) : T where simplify(Γ, T, variant(Tf)), member(Li : Te, Tf), Γ /- Mi : T_, Γ \- T_ <: Te.
Γ /- case(M, Cases) : bot where Γ /- M : T, lcst(Γ, T, bot), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi)] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases).
Γ /- case(M, Cases) : T_ where Γ /- M : T, lcst(Γ, T, variant(Tf)), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, CaseTypes), foldl(join(Γ), bot, CaseTypes, T_).
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- deref(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, ref(T1)).
Γ /- deref(M1) : bot where Γ /- M1 : T, lcst(Γ, T, bot).
Γ /- deref(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, source(T1)).
Γ /- assign(M1, M2) : unit where Γ /- M1 : T, lcst(Γ, T, ref(T1)), Γ /- M2 : T2, Γ \- T2 <: T1.
Γ /- assign(M1, M2) : bot where Γ /- M1 : T, lcst(Γ, T, bot), Γ /- M2 : _.
Γ /- assign(M1, M2) : unit where Γ /- M1 : T, lcst(Γ, T, sink(T1)), Γ /- M2 : T2, subtyping(Γ, T2, T1).
Γ /- loc(l) : _ where !, fail.
Γ /- try(M1, M2) : T where Γ /- M1 : T1, Γ /- M2 : T2, join(Γ, T1, T2, T).
Γ /- error : bot.
Γ /- (fn(TX :: T1) => M2) : all(TX, T1, T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, all(X, T11, T12)), Γ \- T2 <: T11, tsubst(X, T2, T12, T12_).
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' <: %w', [T]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), (Γ, St), (Γ, St_)) :- !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
run(bind(X, bMAbb(M, none)), (Γ, St), ([X - Bind | Γ], St_)) :- Γ /- M : T, evalbinding(Γ, St, bMAbb(M, some(T)), Bind, St_), write(X), show_bind(Γ, Bind, S), writeln(S).
run(bind(X, bMAbb(M, some(T))), (Γ, St), ([X - Bind | Γ], St_)) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, St, bMAbb(M, some(T)), Bind, St_), show_bind(Γ, Bind, S), write(X), writeln(S).
run(bind(X, Bind), (Γ, St), ([X - Bind_ | Γ], St_)) :- evalbinding(Γ, St, Bind, Bind_, St_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, ([], []), _).
:- run([eval((fn(x : bot) -> x))]).
:- run([eval((fn(x : bot) -> x $ x))]).
:- run([eval((fn(x : variant([a : bool, b : bool])) -> x))]).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(r : {[x : (top -> top)]}) -> proj(r, x) $ proj(r, x)) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]})]).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval(let(x, true, x))]).
:- run([eval({[x = true, y = false]})]).
:- run([eval(proj({[x = true, y = false]}, x))]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval(proj({[1 = true, 2 = false]}, 1))]).
:- run([eval(if(true, {[x = true, y = false, a = false]}, {[y = false, x = {[]}, b = false]}))]).
:- run([eval(timesfloat(2.0, 3.14159))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x))![all('X', top, ('X' -> 'X'))])]).
:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval(if(error, true, false))]).
:- run([eval(error $ true)]).
:- run([eval((fn(x : bool) -> x) $ error)]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(zero))]).
:- run([bind('T', bTAbb((nat -> nat))), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval(try(error, true))]).
:- run([eval(try(if(true, error, true), false))]).
:- halt.

