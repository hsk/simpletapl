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
:- use_module(rtg).
w ::= bool | nat | unit | float | string | top | true | false | 0 | error.
syntax(x).
x(X) :- \+ w(X), atom(X).
syntax(floatl).
floatl(F) :- float(F).
syntax(stringl).
stringl(F) :- string(F).
syntax(integer).
syntax(l).
l(L) :- atom(L) ; integer(L).
list(A) ::= [] | [A | list(A)].
k ::= '*' | kArr(k, k).
t ::= bool | nat | unit | float | string | top | bot | x | (t -> t) | {list(l : t)} | variant(list(x : t)) | ref(t) | source(t) | sink(t) | (all(x :: t) => t) | (some(x :: t) => t) | abs(x, k, t) | t $ t.
m ::= true | false | if(m, m, m) | 0 | succ(m) | pred(m) | iszero(m) | unit | floatl | m * m | stringl | x | (fn(x : t) -> m) | m $ m | (let(x) = m in m) | fix(m) | inert(t) | m as t | {list(l = m)} | m # l | case(m, list(x = (x, m))) | tag(x, m, t) | loc(integer) | ref(m) | '!'(m) | m := m | error | try(m, m) | pack(t, m, t) | unpack(x, x, m, m) | (fn(x :: t) => m) | m![t].
n ::= 0 | succ(n).
v ::= true | false | n | unit | floatl | stringl | (fn(x : t) -> m) | {list(l = v)} | tag(x, v, t) | loc(integer) | pack(t, v, t) | (fn(x :: t) => m).
maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
variant(Mf)![(J -> S)] tsubst variant(Mf_) :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
ref(T1)![(J -> S)] tsubst ref(T1_) :- T1![(J -> S)] tsubst T1_.
source(T1)![(J -> S)] tsubst source(T1_) :- T1![(J -> S)] tsubst T1_.
sink(T1)![(J -> S)] tsubst sink(T1_) :- T1![(J -> S)] tsubst T1_.
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
(some(TX :: T1) => T2)![(J -> S)] tsubst (some(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
abs(TX, K, T2)![(J -> S)] tsubst abs(TX, K, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
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
tag(L, M1, T1)![(J -> M)] subst tag(L, M1_, T1) :- M1![(J -> M)] subst M1_.
case(M1, Cases)![(J -> M)] subst case(M1_, Cases_) :- M1![(J -> M)] subst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> M)] subst M1_), Cases, Cases_).
ref(M1)![(J -> M)] subst ref(M1_) :- M1![(J -> M)] subst M1_.
'!'(M1)![(J -> M)] subst '!'(M1_) :- M1![(J -> M)] subst M1_.
(M1 := M2)![(J -> M)] subst (M1_ := M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
loc(L)![(J -> M)] subst loc(L).
try(M1, M2)![(J -> M)] subst try(M1_, M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
error![(J -> M)] subst error.
(fn(TX :: T) => M2)![(J -> M)] subst (fn(TX :: T) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
pack(T1, M2, T3)![(J -> M)] subst pack(T1, M2_, T3) :- M2![(J -> M)] subst M2_.
unpack(TX, X, M1, M2)![(J -> M)] subst unpack(TX, X, M1_, M2_) :- M1![X, (J -> M)] subst2 M1_, M2![X, (J -> M)] subst2 M2_.
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
tag(L, M1, T1)![(J -> S)] tmsubst tag(L, M1_, T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
case(M1, Cases)![(J -> S)] tmsubst case(M1_, Cases_) :- M1![(J -> S)] tmsubst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> S)] subst M1_), Cases, Cases_).
ref(M1)![(J -> S)] tmsubst ref(M1_) :- M1![(J -> S)] tmsubst M1_.
'!'(M1)![(J -> S)] tmsubst '!'(M1_) :- M1![(J -> S)] tmsubst M1_.
(M1 := M2)![(J -> S)] tmsubst (M1_ := M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
loc(L)![(J -> S)] tmsubst loc(L).
try(M1, M2)![(J -> S)] tmsubst try(M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
error![(J -> S)] tmsubst error.
(fn(TX :: T1) => M2)![(J -> S)] tmsubst (fn(TX :: T1_) => M2_) :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
pack(T1, M2, T3)![(J -> S)] tmsubst pack(T1_, M2_, T3_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_, T3![(J -> S)] tsubst T3_.
unpack(TX, X, M1, M2)![(J -> S)] tmsubst unpack(TX, X, M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))).
maketop('*', top).
maketop(kArr(K1, K2), abs('_', K1, K2_)) :- maketop(K2, K2_).
extendstore(St, V1, Len, St_) :- length(St, Len), append(St, [V1], St_).
lookuploc(St, L, R) :- nth0(L, St, R).
updatestore([_ | St], 0, V1, [V1 | St]).
updatestore([V | St], N1, V1, [V | St_]) :- N is N1 - 1, updatestore(St, N, V1, St_).
eval_context(if(M1, M2, M3), ME, if(MH, M2, M3), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(succ(M1), ME, succ(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(pred(M1), ME, pred(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(iszero(M1), ME, iszero(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 * M2, ME, MH * M2, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(V1 * M2, ME, V1 * MH, H) :- \+ v(M2), eval_context(M1, ME, MH, H).
eval_context(M1 $ M2, ME, MH $ M2, H) :- \+ v(M1) -> eval_context(M1, ME, MH, H).
eval_context(V1 $ M2, ME, V1 $ MH, H) :- \+ v(M2) -> eval_context(M2, ME, MH, H).
eval_context((let(X) = M1 in M2), ME, (let(X) = MH in M2), H) :- \+ v(M1) -> eval_context(M1, ME, MH, H).
eval_context(fix(M1), ME, fix(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 as T, ME, MH as T, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 # L, ME, MH # L, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(tag(L, M1, T), ME, tag(L, MH, T), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(case(M1, Branches), ME, case(MH, Branches), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(ref(M1), ME, ref(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context('!'(M1), ME, '!'(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 := M2, ME, MH := M2, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(V1 := M2, ME, V1 := MH, H) :- \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(M1![T], ME, MH![T], H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(pack(T1, M2, T3), ME, pack(T1, MH, T3), H) :- \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(unpack(TX, X, M1, M2), ME, unpack(TX, X, MH, M2), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context({Mf}, ME, {MH}, H) :- \+ v(M1), e(Mf, ME, MH, H).
eval_context(try(M1, M2), M1, try(H, M2), H).
eval_context(M1, M1, H, H) :- \+ v(M1).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ / St /- if(true, M2, M3) ==> M2 / St.
Γ / St /- if(false, M2, M3) ==> M3 / St.
Γ / St /- pred(0) ==> 0 / St.
Γ / St /- pred(succ(NV1)) ==> NV1 / St where n(NV1).
Γ / St /- iszero(0) ==> true / St.
Γ / St /- iszero(succ(NV1)) ==> false / St where n(NV1).
Γ / St /- F1 * F2 ==> F3 / St where float(F1), float(F2), F3 is F1 * F2.
Γ / St /- X ==> M / St where x(X), getb(Γ, X, bMAbb(M, _)).
Γ / St /- (fn(X : _) -> M12) $ V2 ==> R / St where v(V2), M12![(X -> V2)] subst R.
Γ / St /- (let(X) = V1 in M2) ==> M2_ / St where v(V1), M2![(X -> V1)] subst M2_.
Γ / St /- fix((fn(X : T11) -> M12)) ==> M / St where M12![(X -> fix((fn(X : T11) -> M12)))] subst M.
Γ / St /- V1 as _ ==> V1 / St where v(V1).
Γ / St /- {Mf} # L ==> M / St where member(L = M, Mf).
Γ / St /- case(tag(L, V11, _), Bs) ==> M_ / St where v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- '!'(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- (loc(L) := V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- (fn(X :: _) => M11)![T2] ==> M11_ / St_ where M11![(X -> T2)] tmsubst M11_.
Γ / St /- unpack(_, X, pack(T11, V12, _), M2) ==> M2__ / St where v(V12), subst(X, V12, M2_), M2_![(X -> T11)] tmsubst M2__.
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
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T) :- x(X), gettabb(Γ, X, T).
compute(Γ, abs(X, _, T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
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
Γ /- top == top.
Γ /- X == T :- x(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- x(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- x(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- variant(Sf) == variant(Tf) :- length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf).
Γ /- ref(S) == ref(T) :- Γ /- S = T.
Γ /- source(S) == source(T) :- Γ /- S = T.
Γ /- sink(S) == sink(T) :- Γ /- S = T.
Γ /- (all(TX :: S1) => S2) == (all(_ :: T1) => T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- (some(TX :: S1) => S2) == (some(_ :: T1) => T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- abs(TX, K1, S2) == abs(_, K1, T2) :- [TX - bName | g] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !.
Γ /- T :: K where writeln(error : kindof(T, K)), fail.
Γ \- X :: '*' where x(X), \+ member(X - _, Γ).
Γ \- X :: K where x(X), getb(Γ, X, bTVar(T)), Γ /- T :: K, !.
Γ \- X :: K where x(X), !, getb(Γ, X, bTAbb(_, some(K))).
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- {Tf} :: '*' where maplist([L : S] >> (Γ /- S :: '*'), Tf).
Γ \- variant(Tf) :: '*' where maplist([L : S] >> (Γ /- S :: '*'), Tf).
Γ \- ref(T) :: '*' where Γ /- T :: '*'.
Γ \- source(T) :: '*' where Γ /- T :: '*'.
Γ \- sink(T) :: '*' where Γ /- T :: '*'.
Γ \- (all(TX :: T1) => T2) :: '*' where !, [TX - bTVar(T1) | Γ] /- T2 :: '*'.
Γ \- abs(TX, K1, T2) :: kArr(K1, K) where !, maketop(K1, T1), [TX - bTVar(T1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: kArr(K11, K12), Γ /- T2 :: K11.
Γ \- (some(TX :: T1) => T2) :: '*' where !, [TX - bTVar(T1) | Γ] /- T2 :: '*'.
Γ \- T :: '*'.
promote(Γ, X, T) :- x(X), getb(Γ, X, bTVar(T)).
promote(Γ, S $ T, S_ $ T) :- promote(Γ, S, S_).
Γ /- S <: T where Γ /- S = T.
Γ /- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- bot <: _.
Γ \- X <: T where x(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ \- variant(SF) <: variant(TF) where maplist([L : S] >> (member(L : T, TF), Γ /- S <: T), SF).
Γ \- ref(S) <: ref(T) where Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) <: source(T) where Γ /- S <: T.
Γ \- source(S) <: source(T) where Γ /- S <: T.
Γ \- ref(S) <: sink(T) where Γ /- T <: S.
Γ \- sink(S) <: sink(T) where Γ /- T <: S.
Γ \- T1 $ T2 <: T where promote(Γ, T1 $ T2, S), Γ /- S <: T.
Γ \- abs(TX, K1, S2) <: abs(_, K1, T2) where maketop(K1, T1), [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- (some(TX :: S1) => S2) <: (some(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ /- S /\ T : T :- Γ /- S <: T.
Γ /- S /\ T : S :- Γ /- T <: S.
Γ /- S /\ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : R.
Γ \- {SF} /\ {TF} : {UF_} :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S /\ T : T_), UF, UF_).
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 /\ T2 : T2_.
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : top.
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
Γ \- (all(TX :: S1) => S2) \/ (all(_ :: T1) => T2) : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 \/ T2 : T2_.
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
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- M1 * M2 : float where Γ /- M1 : T1, Γ /- T1 <: float, Γ /- M2 : T2, Γ /- T2 <: float.
Γ /- X : string where string(X).
Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), !, Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- M1 $ M2 : bot where !, Γ /- M1 : T1, lcst(Γ, T1, bot), Γ /- M2 : T2.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- T12 <: T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- T :: '*', Γ /- M1 : T1, Γ /- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf), !.
Γ /- (M1 # L) : T where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- tag(Li, Mi, T) : T where simplify(Γ, T, variant(Tf)), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ <: Te.
Γ /- case(M, Cases) : bot where Γ /- M : T, lcst(Γ, T, bot), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi)] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases).
Γ /- case(M, Cases) : T_ where Γ /- M : T, lcst(Γ, T, variant(Tf)), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, CaseTypes), foldl(join(Γ), bot, CaseTypes, T_).
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- '!'(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, ref(T1)).
Γ /- '!'(M1) : bot where Γ /- M1 : T, lcst(Γ, T, bot).
Γ /- '!'(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, source(T1)).
Γ /- (M1 := M2) : unit where Γ /- M1 : T, lcst(Γ, T, ref(T1)), Γ /- M2 : T2, Γ /- T2 <: T1.
Γ /- (M1 := M2) : bot where Γ /- M1 : T, lcst(Γ, T, bot), Γ /- M2 : _.
Γ /- (M1 := M2) : unit where Γ /- M1 : T, lcst(Γ, T, sink(T1)), Γ /- M2 : T2, subtyping(Γ, T2, T1).
Γ /- loc(l) : _ where !, fail.
Γ /- try(M1, M2) : T where Γ /- M1 : T1, Γ /- M2 : T2, Γ /- T1 /\ T2 : T.
Γ /- error : bot where !.
Γ /- pack(T1, M2, T) : T where Γ /- T :: '*', simplify(Γ, T, (some(Y :: TBound) => T2)), Γ /- T1 <: TBound, Γ /- M2 : S2, T2![(Y -> T1)] tsubst T2_, Γ /- S2 <: T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, lcst(Γ, T1, (some(_ :: TBound) => T11)), [X - bVar(T11), TX - bTVar(TBound) | Γ] /- M2 : T2.
Γ /- (fn(TX :: T1) => M2) : (all(TX :: T1) => T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)), Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' <: %w', [T]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T, none), R) :- Γ /- T :: K, swritef(R, ' :: %w', [K]).
show_bind(Γ, bTAbb(T, some(K)), R) :- swritef(R, ' :: %w', [K]).
check_bind(Γ, bName, bName).
check_bind(Γ, bTVar(K), bTVar(K)).
check_bind(Γ, bTAbb(T, none), bTAbb(T, some(K))) :- Γ /- T :: K.
check_bind(Γ, bTAbb(T, some(K)), bTAbb(T, some(K))) :- Γ /- T :: K.
check_bind(Γ, bVar(T), bVar(T)).
check_bind(Γ, bMAbb(M, none), bMAbb(M, some(T))) :- Γ /- M : T.
check_bind(Γ, bMAbb(M, some(T)), bMAbb(M, some(T))) :- Γ /- M : T1, Γ /- T1 = T.
check_someBind(TBody, pack(_, T12, _), bMAbb(T12, some(TBody))).
check_someBind(TBody, _, bVar(TBody)).
run(eval(M), (Γ, St), (Γ, St_)) :- !, m(M), !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
run(bind(X, Bind), (Γ, St), ([X - Bind_ | Γ], St_)) :- check_bind(Γ, Bind, Bind1), evalbinding(Γ, St, Bind1, Bind_, St_), write(X), show_bind(Γ, Bind_, R), writeln(R).
run(someBind(TX, X, M), (Γ, St), ([X - B, TX - bTVar(K) | Γ], St_)) :- !, Γ /- M : T, simplify(Γ, T, (some(_ :: K) => TBody)), Γ / St /- M ==>> M_ / St_, check_someBind(TBody, M_, B), writeln(TX), write(X), write(' : '), writeln(TBody).
run(Ls) :- foldl(run, Ls, ([], []), _).
:- run([eval((fn(x : bot) -> x))]).
:- run([eval((fn(x : bot) -> x $ x))]).
:- run([eval((fn(x : variant([a : bool, b : bool])) -> x))]).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(r : {[x : (top -> top)]}) -> (r # x) $ (r # x)) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]})]).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval({[x = true, y = false]})]).
:- run([eval({[x = true, y = false]} # x)]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval({[1 = true, 2 = false]} # 1)]).
:- run([eval(if(true, {[x = true, y = false, a = false]}, {[y = false, x = {[]}, b = false]}))]).
:- run([eval(try(error, true))]).
:- run([eval(try(if(true, error, true), false))]).
:- run([eval(2.0 * 3.14159)]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval(if(error, true, false))]).
:- run([eval(error $ true)]).
:- run([eval((fn(x : bool) -> x) $ error)]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(0))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- halt.

