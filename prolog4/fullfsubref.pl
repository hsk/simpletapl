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
val(X) :- X \= bool, X \= nat, X \= unit, X \= float, X \= string, X \= top, X \= bot, X \= true, X \= false, X \= zero, X \= error, atom(X).
l(L) :- atom(L) ; integer(L).
t(T) :- T = bool ; T = nat ; T = unit ; T = float ; T = string ; T = top ; T = bot ; T = X, val(X) ; T = (T1 -> T2), t(T1), t(T2) ; T = {Tf}, maplist([X : T1] >> (l(X), t(T1)), Tf) ; T = variant(Tf), maplist([X : T1] >> (val(X), t(T1)), Tf) ; T = ref(T1), t(T1) ; T = source(T1), t(T1) ; T = sink(T1), t(T1) ; T = all(X, T1, T2), val(X), t(T1), t(T2).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = zero ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1) ; M = unit ; M = F, float(F) ; M = timesfloat(M1, M2), m(M1), m(M2) ; M = X, string(X) ; M = X, val(X) ; M = (fn(X : T1) -> M1), val(X), t(T1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = let(X, M1, M2), val(X), m(M1), m(M2) ; M = fix(M1), m(M1) ; M = inert(T1), t(T1) ; M = as(M1, T1), m(M1), t(T1) ; M = {Tf}, maplist([X = M1] >> (l(X), m(M1)), Mf) ; M = proj(M1, L), m(M1), l(L) ; M = case(M1, Cases), m(M1), maplist([X = (X1, M2)] >> (val(X), (val(X1), m(M2))), Cases) ; M = tag(X, M1, T1), val(X), m(M1), t(T1) ; M = loc(I), integer(I) ; M = ref(M1), m(M1) ; M = deref(M1), m(M1) ; M = assign(M1, M2), m(M1), m(M2) ; M = error ; M = try(M1, M2), m(M1), m(M2) ; M = (fn(TX :: T1) => M1), val(TX), t(T1), m(M1) ; M = M1![T1], m(M1), t(T1).
maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
top![(J -> S)] tsubst top.
bot![(J -> S)] tsubst bot.
J![(J -> S)] tsubst S :- val(J).
X![(J -> S)] tsubst X :- val(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
variant(Mf)![(J -> S)] tsubst variant(Mf_) :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
ref(T1)![(J -> S)] tsubst ref(T1_) :- T1![(J -> S)] tsubst T1_.
source(T1)![(J -> S)] tsubst source(T1_) :- T1![(J -> S)] tsubst T1_.
sink(T1)![(J -> S)] tsubst sink(T1_) :- T1![(J -> S)] tsubst T1_.
all(TX, T1, T2)![(J -> S)] tsubst all(TX, T1_, T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
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
unit![(J -> M)] subst unit.
F1![(J -> M)] subst F1 :- float(F1).
timesfloat(M1, M2)![(J -> M)] subst timesfloat(M1_, M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
X![(J -> M)] subst X :- string(X).
J![(J -> M)] subst M :- val(J).
X![(J -> M)] subst X :- val(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
let(X, M1, M2)![(J -> M)] subst let(X, M1_, M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
fix(M1)![(J -> M)] subst fix(M1_) :- M1![(J -> M)] subst M1_.
inert(T1)![(J -> M)] subst inert(T1).
as(M1, T1)![(J -> M)] subst as(M1_, T1) :- M1![(J -> M)] subst M1_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
proj(M1, L)![(J -> M)] subst proj(M1_, L) :- M1![(J -> M)] subst M1_.
tag(L, M1, T1)![(J -> M)] subst tag(L, M1_, T1) :- M1![(J -> M)] subst M1_.
case(M1, Cases)![(J -> M)] subst case(M1_, Cases_) :- M1![(J -> M)] subst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> M)] subst M1_), Cases, Cases_).
ref(M1)![(J -> M)] subst ref(M1_) :- M1![(J -> M)] subst M1_.
deref(M1)![(J -> M)] subst deref(M1_) :- M1![(J -> M)] subst M1_.
assign(M1, M2)![(J -> M)] subst assign(M1_, M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
loc(L)![(J -> M)] subst loc(L).
try(M1, M2)![(J -> M)] subst try(M1_, M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
error![(J -> M)] subst error.
(fn(TX :: T1) => M2)![(J -> M)] subst (fn(TX :: T1) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_, M3![(J -> S)] tmsubst M3_.
zero![(J -> S)] tmsubst zero.
succ(M1)![(J -> S)] tmsubst succ(M1_) :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_) :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_) :- M1![(J -> S)] tmsubst M1_.
unit![(J -> S)] tmsubst unit.
F1![(J -> S)] tmsubst F1 :- float(F1).
timesfloat(M1, M2)![(J -> S)] tmsubst timesfloat(M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
X![(J -> S)] tmsubst X :- string(X).
X![(J -> S)] tmsubst X :- val(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
let(X, M1, M2)![(J -> S)] tmsubst let(X, M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
fix(M1)![(J -> S)] tmsubst fix(M1_) :- M1![(J -> S)] tmsubst M1_.
inert(T1)![(J -> S)] tmsubst inert(T1).
as(M1, T1)![(J -> S)] tmsubst as(M1_, T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
{Mf}![(J -> S)] tmsubst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> S)] tmsubst Mi_), Mf, Mf_).
proj(M1, L)![(J -> S)] tmsubst proj(M1_, L) :- M1![(J -> S)] tmsubst M1_.
tag(L, M1, T1)![(J -> S)] tmsubst tag(L, M1_, T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
case(M1, Cases)![(J -> S)] tmsubst case(M1_, Cases_) :- M1![(J -> S)] tmsubst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> S)] subst M1_), Cases, Cases_).
ref(M1)![(J -> S)] tmsubst ref(M1_) :- M1![(J -> S)] tmsubst M1_.
deref(M1)![(J -> S)] tmsubst deref(M1_) :- M1![(J -> S)] tmsubst M1_.
assign(M1, M2)![(J -> S)] tmsubst assign(M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
loc(L)![(J -> S)] tmsubst loc(L).
try(M1, M2)![(J -> S)] tmsubst try(M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
error![(J -> S)] tmsubst error.
(fn(TX :: T1) => M2)![(J -> S)] tmsubst (fn(TX :: T1_) => M2_) :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
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
Γ / St /- (fn(X : _) -> M12) $ V2 ==> R / St where v(V2), M12![(X -> V2)] subst R.
Γ / St /- let(X, V1, M2) ==> M2_ / St where v(V1), M2![(X -> V1)] subst M2_.
Γ / St /- fix((fn(X : T11) -> M12)) ==> M / St where M12![(X -> fix((fn(X : T11) -> M12)))] subst M.
Γ / St /- as(V1, _) ==> V1 / St where v(V1).
Γ / St /- proj({Mf}, L) ==> M / St where member(L = M, Mf).
Γ / St /- case(tag(L, V11, _), Bs) ==> M_ / St where v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- deref(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- assign(loc(L), V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- (fn(X) => M11)![T2] ==> M11_ / St_ where M11![(X -> T2)] tmsubst M11_.
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
Γ /- S <: T where Γ /- S = T.
Γ /- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- bot <: _.
Γ \- X <: T where val(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ \- variant(SF) <: variant(TF) where maplist([L : S] >> (member(L : T, TF), Γ /- S <: T), SF).
Γ \- ref(S) <: ref(T) where Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) <: source(T) where Γ /- S <: T.
Γ \- source(S) <: source(T) where Γ /- S <: T.
Γ \- ref(S) <: sink(T) where Γ /- T <: S.
Γ \- sink(S) <: sink(T) where Γ /- T <: S.
Γ \- all(TX, S1, S2) <: all(_, T1, T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ /- S /\ T : T :- Γ /- S <: T.
Γ /- S /\ T : S :- Γ /- T <: S.
Γ /- S /\ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : R.
Γ \- {SF} /\ {TF} : {UF_} :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S /\ T : T_), UF, UF_).
Γ \- all(TX, S1, S2) /\ all(_, T1, T2) : all(TX, S1, T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 /\ T2 : T2_.
Γ \- all(TX, S1, S2) /\ all(_, T1, T2) : top.
Γ \- (S1 -> S2) /\ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 \/ T1 : S_, Γ /- S2 /\ T2 : T_.
Γ \- ref(S) /\ ref(T) : ref(S) :- Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) /\ ref(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- source(S) /\ source(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- ref(S) /\ source(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- source(S) /\ ref(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- sink(S) /\ sink(T) : sink(T_) :- Γ /- S \/ T : T_.
Γ \- ref(S) /\ sink(T) : sink(T_) :- Γ /- S \/ T : T_.
Γ \- sink(S) /\ ref(T) : sink(T_) :- Γ /- S \/ T : T_.
Γ \- _ /\ _ : top.
Γ /- S \/ T : S :- Γ /- S <: T.
Γ /- S \/ T : T :- Γ /- T <: S.
Γ /- S \/ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ \/ T_ : R.
Γ \- {SF} \/ {TF} : {UF_} :- maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S \/ T : T_ ; T_ = S), SF, SF_), include([L : _] >> (\+ member(L : _, SF)), TF, TF_), append(SF_, TF_, UF_).
Γ \- all(TX, S1, S2) \/ all(_, T1, T2) : all(TX, S1, T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 \/ T2 : T2_.
Γ \- (S1 -> S2) \/ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 /\ T1 : S_, Γ /- S2 \/ T2 : T_.
Γ \- ref(S) \/ ref(T) : ref(T) :- Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) \/ ref(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- source(S) \/ source(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- ref(S) \/ source(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- source(S) \/ ref(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- sink(S) \/ sink(T) : sink(T_) :- Γ /- S /\ T : T_.
Γ \- ref(S) \/ sink(T) : sink(T_) :- Γ /- S /\ T : T_.
Γ \- sink(S) \/ ref(T) : sink(T_) :- Γ /- S /\ T : T_.
meet2(_, _, bot).
lcst(Γ, S, T) :- simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T).
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T where Γ /- M1 : T1, Γ /- T1 <: bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 /\ T3 : T.
Γ /- zero : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- timesfloat(M1, M2) : float where Γ /- M1 : T1, Γ /- T1 <: float, Γ /- M2 : T2, Γ /- T2 <: float.
Γ /- X : string where string(X).
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : bot where Γ /- M1 : T1, Γ /- M2 : T2, lcst(Γ, T1, bot).
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- T12 <: T11.
Γ /- fix(M1) : bot where Γ /- M1 : T1, lcst(Γ, T1, bot).
Γ /- inert(T) : T.
Γ /- as(M1, T) : T where Γ /- M1 : T1, Γ /- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- proj(M1, L) : T where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- proj(M1, L) : bot where Γ /- M1 : T1, lcst(Γ, T1, bot).
Γ /- tag(Li, Mi, T) : T where simplify(Γ, T, variant(Tf)), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ <: Te.
Γ /- case(M, Cases) : bot where Γ /- M : T, lcst(Γ, T, bot), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi)] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases).
Γ /- case(M, Cases) : T_ where Γ /- M : T, lcst(Γ, T, variant(Tf)), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, CaseTypes), foldl(join(Γ), bot, CaseTypes, T_).
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- deref(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, ref(T1)).
Γ /- deref(M1) : bot where Γ /- M1 : T, lcst(Γ, T, bot).
Γ /- deref(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, source(T1)).
Γ /- assign(M1, M2) : unit where Γ /- M1 : T, lcst(Γ, T, ref(T1)), Γ /- M2 : T2, Γ /- T2 <: T1.
Γ /- assign(M1, M2) : bot where Γ /- M1 : T, lcst(Γ, T, bot), Γ /- M2 : _.
Γ /- assign(M1, M2) : unit where Γ /- M1 : T, lcst(Γ, T, sink(T1)), Γ /- M2 : T2, subtyping(Γ, T2, T1).
Γ /- loc(l) : _ where !, fail.
Γ /- try(M1, M2) : T where Γ /- M1 : T1, Γ /- M2 : T2, Γ /- T1 /\ T2 : T.
Γ /- error : bot.
Γ /- (fn(TX :: T1) => M2) : all(TX, T1, T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, all(X, T11, T12)), Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' <: %w', [T]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), (Γ, St), (Γ, St_)) :- !, m(M), !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
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

