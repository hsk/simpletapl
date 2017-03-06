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

% 変数
% キーワード以外のatomが変数
val(X) where X \= bool, X \= nat, X \= unit, X \= float, X \= string, X \= top, X \= true, X \= false, X \= zero, X \= error, atom(X).

% 型置換
tsubst(J, S, bool, bool).
tsubst(J, S, nat, nat).
tsubst(J, S, unit, unit).
tsubst(J, S, float, float).
tsubst(J, S, string, string).
tsubst(J, S, top, top).
tsubst(J, S, J, S)                                 where val(J).
tsubst(J, S, X, X)                                 where val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_))             where tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, {Mf}, {Mf_})                          where maplist([L : T, L : T_] >> tsubst(J, S, T, T_), Mf, Mf_).
tsubst(J, S, variant(Mf), variant(Mf_))            where maplist([L : T, L : T_] >> tsubst(J, S, T, T_), Mf, Mf_).
tsubst(J, S, ref(T1), ref(T1_))                    where tsubst(J, S, T1, T1_).
tsubst(J, S, source(T1), source(T1_))              where tsubst(J, S, T1, T1_).
tsubst(J, S, sink(T1), sink(T1_))                  where tsubst(J, S, T1, T1_).
tsubst(J, S, all(TX, T1, T2), all(TX, T1_, T2_))   where tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, some(TX, T1, T2), some(TX, T1_, T2_)) where tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, abs(TX, K, T2), abs(TX, K, T2_))      where tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, T1 $ T2, T1_ $ T2_)                   where tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst2(X, X, S, T, T).
tsubst2(X, J, S, T, T_)                            where tsubst(J, S, T, T_).

% 項置換
subst(J, M, true, true).
subst(J, M, false, false).
subst(J, M, if(M1, M2, M3), if(M1_, M2_, M3_))              where subst(J, M, M1, M1_), subst(J, M, M2, M2_), subst(J, M, M3, M3_).
subst(J, M, zero, zero).
subst(J, M, succ(M1), succ(M1_))                            where subst(J, M, M1, M1_).
subst(J, M, pred(M1), pred(M1_))                            where subst(J, M, M1, M1_).
subst(J, M, iszero(M1), iszero(M1_))                        where subst(J, M, M1, M1_).
subst(J, M, unit, unit).
subst(J, M, F1, F1)                                         where float(F1).
subst(J, M, timesfloat(M1, M2), timesfloat(M1_, M2_))       where subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, X, X)                                           where string(X).
subst(J, M, J, M)                                           where val(J).
subst(J, M, X, X)                                           where val(X).
subst(J, M, (fn(X : T1) -> M2), (fn(X : T1) -> M2_))        where subst2(X, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_)                             where subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, let(X, M1, M2), let(X, M1_, M2_))               where subst(J, M, M1, M1_), subst2(X, J, M, M2, M2_).
subst(J, M, fix(M1), fix(M1_))                              where subst(J, M, M1, M1_).
subst(J, M, inert(T1), inert(T1)).
subst(J, M, as(M1, T1), as(M1_, T1))                        where subst(J, M, M1, M1_).
subst(J, M, {Mf}, {Mf_})                                    where maplist([L = Mi, L = Mi_] >> subst(J, M, Mi, Mi_), Mf, Mf_).
subst(J, M, proj(M1, L), proj(M1_, L))                      where subst(J, M, M1, M1_).
subst(J, M, tag(L, M1, T1), tag(L, M1_, T1))                where subst(J, M, M1, M1_).
subst(J, M, case(M1, Cases), case(M1_, Cases_))             where subst(J, M, M1, M1_),
                                                                  maplist([L = (X, M1), L = (X, M1_)] >> subst(J, M, M1, M1_), Cases, Cases_).
subst(J, M, ref(M1), ref(M1_))                              where subst(J, M, M1, M1_).
subst(J, M, deref(M1), deref(M1_))                          where subst(J, M, M1, M1_).
subst(J, M, assign(M1, M2), assign(M1_, M2_))               where subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, loc(L), loc(L)).
subst(J, M, try(M1, M2), try(M1_, M2_))                     where subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, error, error).
subst(J, M, (fn(TX :: T) => M2), (fn(TX :: T) => M2_))      where subst(J, M, M2, M2_).
subst(J, M, M1![T2], M1_![T2])                              where subst(J, M, M1, M1_).
subst(J, M, pack(T1, M2, T3), pack(T1, M2_, T3))            where subst(J, M, M2, M2_).
subst(J, M, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) where subst2(X, J, M, M1, M1_), subst2(X, J, M, M2, M2_).
subst(J, M, S, _)                                           where writeln(error : subst(J, M, S)), fail.
subst2(J, J, M, S, S).
subst2(X, J, M, S, M_)                                      where subst(J, M, S, M_).

% 項内型置換
tmsubst(J, S, true, true).
tmsubst(J, S, false, false).
tmsubst(J, S, if(M1, M2, M3), if(M1_, M2_, M3_))              where tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_), tmsubst(J, S, M3, M3_).
tmsubst(J, S, zero, zero).
tmsubst(J, S, succ(M1), succ(M1_))                            where tmsubst(J, S, M1, M1_).
tmsubst(J, S, pred(M1), pred(M1_))                            where tmsubst(J, S, M1, M1_).
tmsubst(J, S, iszero(M1), iszero(M1_))                        where tmsubst(J, S, M1, M1_).
tmsubst(J, M, unit, unit).
tmsubst(J, M, F1, F1)                                         where float(F1).
tmsubst(J, M, timesfloat(M1, M2), timesfloat(M1_, M2_))       where tmsubst(J, M, M1, M1_), tmsubst(J, M, M2, M2_).
tmsubst(J, M, X, X)                                           where string(X).
tmsubst(J, S, X, X)                                           where val(X).
tmsubst(J, S, (fn(X : T1) -> M2), (fn(X : T1_) -> M2_))       where tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, M1 $ M2, M1_ $ M2_)                             where tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, let(X, M1, M2), let(X, M1_, M2_))               where tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, M, fix(M1), fix(M1_))                              where tmsubst(J, M, M1, M1_).
tmsubst(J, M, inert(T1), inert(T1)).
tmsubst(J, S, as(M1, T1), as(M1_, T1_))                       where tmsubst(J, S, M1, M1_), tsubst(J, S, T1, T1_).
tmsubst(J, M, {Mf}, {Mf_})                                    where maplist([L = Mi, L = Mi_] >> tmsubst(J, M, Mi, Mi_), Mf, Mf_).
tmsubst(J, M, proj(M1, L), proj(M1_, L))                      where tmsubst(J, M, M1, M1_).
tmsubst(J, S, tag(L, M1, T1), tag(L, M1_, T1_))               where tmsubst(J, S, M1, M1_), tsubst(J, S, T1, T1_).
tmsubst(J, S, case(M1, Cases), case(M1_, Cases_))             where tmsubst(J, S, M1, M1_),
                                                                    maplist([L = (X, M1), L = (X, M1_)] >> subst(J, S, M1, M1_), Cases, Cases_).
tmsubst(J, S, ref(M1), ref(M1_))                              where tmsubst(J, S, M1, M1_).
tmsubst(J, S, deref(M1), deref(M1_))                          where tmsubst(J, S, M1, M1_).
tmsubst(J, S, assign(M1, M2), assign(M1_, M2_))               where tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, loc(L), loc(L)).
tmsubst(J, S, try(M1, M2), try(M1_, M2_))                     where tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, error, error).
tmsubst(J, S, (fn(TX :: T1) => M2), (fn(TX :: T1_) => M2_))   where tsubst2(TX, J, S, T1, T1_), tmsubst2(TX, J, S, M2, M2_).
tmsubst(J, S, M1![T2], M1_![T2_])                             where tmsubst(J, S, M1, M1_), tsubst(J, S, T2, T2_).
tmsubst(J, S, pack(T1, M2, T3), pack(T1_, M2_, T3_))          where tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_), tsubst(J, S, T3, T3_).
tmsubst(J, S, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) where tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst2(X, X, S, T, T).
tmsubst2(X, J, S, T, T_)                                      where tmsubst(J, S, T, T_).

% バインディング取得
getb(Γ, X, B)                            where member(X-B, Γ).

% 型取得
gett(Γ, X, T)                            where getb(Γ, X, bVar(T)).
gett(Γ, X, T)                            where getb(Γ, X, bMAbb(_, some(T))).

% カインド型変換
maketop('*', top).
maketop(kArr(K1, K2), abs('_', K1, K2_)) where maketop(K2, K2_).

% 整数値
n(zero).
n(succ(M1))                              where n(M1).

% 値
v(true).
v(false).
v(M)                                     where n(M).
v(unit).
v(F1)                                    where float(F1).
v(X)                                     where string(X).
v((fn(_ : _) -> _)).
v({Mf})                                  where maplist([L = M] >> v(M), Mf).
v(tag(_, M1, _))                         where v(M1).
v(loc(_)).
v(pack(_, V1, _))                        where v(V1).
v((fn(_ :: _) => _)).

% ストアの拡張
extendstore(St, V1, Len, St_)            where length(St, Len), append(St, [V1], St_).
% ストア検索
lookuploc(St, L, R)                      where nth0(L, St, R).
% ストアアップデート
updatestore([_|St], 0, V1, [V1|St]).
updatestore([V|St], N1, V1, [V|St_])     where N is N1-1, updatestore(St, N, V1, St_).

% 評価文脈
eval_context(if(M1, M2, M3), ME, if(MH, M2, M3), H)               where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(succ(M1), ME, succ(MH), H)                           where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(pred(M1), ME, pred(MH), H)                           where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(iszero(M1), ME, iszero(MH), H)                       where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(timesfloat(M1, M2), ME, timesfloat(MH, M2), H)       where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(timesfloat(V1, M2), ME, timesfloat(V1, MH), H)       where \+ v(M2), eval_context(M1, ME, MH, H).
eval_context(M1 $ M2, ME, MH $ M2, H)                             where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(V1 $ M2, ME, V1 $ MH, H)                             where \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(let(X, M1, M2), ME, let(X, MH, M2), H)               where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(fix(M1), ME, fix(MH), H)                             where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(as(M1, T), ME, as(MH, T), H)                         where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(proj(M1, L), ME, proj(MH, L), H)                     where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(tag(L, M1, T), ME, tag(L, MH, T), H)                 where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(case(M1, Branches), ME, case(MH, Branches), H)       where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(ref(M1), ME, ref(MH), H)                             where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(deref(M1), ME, deref(MH), H)                         where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(assign(M1, M2), ME, assign(MH, M2), H)               where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(assign(V1, M2), ME, assign(V1, MH), H)               where \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(M1![T], ME, MH![T], H)                               where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(pack(T1, M2, T3), ME, pack(T1, MH, T3), H)           where \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(unpack(TX, X, M1, M2), ME, unpack(TX, X, MH, M2), H) where \+ v(M1), eval_context(M1, ME, MH, H).
eval_context({Mf}, ME, {MH}, H)                                   where \+ v(M1), e(Mf, ME, MH, H).
eval_context(try(M1, M2), M1, try(H, M2), H).
eval_context(M1, M1, H, H)                                        where \+ v(M1).

% レコードの評価文脈
e([L = M|Mf], M,  [L = M_|Mf], M_)                                where \+ v(M).
e([L = M|Mf], M1, [L = M|Mf_], M_)                                where v(M), e(Mf, M1, Mf_, M_).

% 評価規則
Γ/St /- if(true, M2, M3)                    ==> M2/St.
Γ/St /- if(false, M2, M3)                   ==> M3/St.
Γ/St /- pred(zero)                          ==> zero/St.
Γ/St /- pred(succ(NV1))                     ==> NV1/St           where n(NV1).
Γ/St /- iszero(zero)                        ==> true/St.
Γ/St /- iszero(succ(NV1))                   ==> false/St         where n(NV1).
Γ/St /- timesfloat(F1, F2)                  ==> F3/St            where float(F1), float(F2), F3 is F1 * F2.
Γ/St /- X                                   ==> M/St             where val(X), getb(Γ, X, bMAbb(M, _)).
Γ/St /- (fn(X : _) -> M12) $ V2             ==> R/St             where v(V2), subst(X, V2, M12, R).
Γ/St /- let(X, V1, M2)                      ==> M2_/St           where v(V1), subst(X, V1, M2, M2_).
Γ/St /- fix((fn(X : T11) -> M12))           ==> M/St             where subst(X, fix((fn(X : T11) -> M12)), M12, M).
Γ/St /- as(V1, _)                           ==> V1/St            where v(V1).
Γ/St /- proj({Mf}, L)                       ==> M/St             where member(L = M, Mf).
Γ/St /- case(tag(L, V11, _), Bs)            ==> M_/St            where v(V11), member(L = (X, M), Bs), subst(X, V11, M, M_).
Γ/St /- ref(V1)                             ==> loc(L)/St_       where v(V1), extendstore(St, V1, L, St_).
Γ/St /- deref(loc(L))                       ==> V1/St            where lookuploc(St, L, V1).
Γ/St /- assign(loc(L), V2)                  ==> unit/St_         where v(V2), updatestore(St, L, V2, St_).
Γ/St /- (fn(X :: _) => M11)![T2]            ==> M11_/St_         where tmsubst(X, T2, M11, M11_).
Γ/St /- unpack(_, X, pack(T11, V12, _), M2) ==> M2__/St          where v(V12), subst(X, V12, M2_), tmsubst(X, T11, M2_, M2__).
Γ/St /- try(error, M2)                      ==> M2/St.
Γ/St /- try(V1, M2)                         ==> V1/St            where v(V1).
Γ/St /- try(M1, M2)                         ==> try(M1_, M2)/St_ where Γ/St /- M1 ==> M1_/St_.
Γ/St /- error                               ==> _/_              where !, fail.
Γ/St /- M                                   ==> error/St         where eval_context(M, error, _, _), !.
Γ/St /- M                                   ==> error/St         where eval_context(M, M, _, _), !, fail.
Γ/St /- M                                   ==> M_/St_           where eval_context(M, ME, M_, H), Γ/St /- ME ==> H/St_.
Γ/St /- M                                  ==>> M_/St_           where Γ/St /- M ==> M1/St1, Γ/St1 /- M1 ==>> M_/St_.
Γ/St /- M                                  ==>> M/St.

evalbinding(Γ, St, bMAbb(M, T), bMAbb(M_, T), St_)               where Γ/St /- M ==>> M_/St_.
evalbinding(Γ, St, Bind, Bind, St).

gettabb(Γ, X, T)                          where getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T)                          where val(X), gettabb(Γ, X, T).
compute(Γ, abs(X, _, T12) $ T2, T)        where tsubst(X, T2, T12, T).
simplify(Γ, T1 $ T2, T_)                  where simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_)                        where simplify2(Γ, T, T_).
simplify2(Γ, T, T_)                       where compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).

maplist2(_, [], []).
maplist2(F, [X|Xs], [Y|Ys])               where call(F, X, Y), maplist2(F, Xs, Ys).

Γ /-                S  = T                where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.

Γ /-             bool == bool.
Γ /-              nat == nat.
Γ /-             unit == unit.
Γ /-            float == float.
Γ /-           string == string.
Γ /-              top == top.
Γ /-                X == T                where val(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /-                S == X                where val(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /-                X == X                where val(X).
Γ /-       (S1 -> S2) == (T1 -> T2)       where Γ /- S1 = T1, Γ /- S2 = T2.
Γ /-             {Sf} == {Tf}             where length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /-      variant(Sf) == variant(Tf)      where length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf).
Γ /-           ref(S) == ref(T)           where Γ /- S = T.
Γ /-        source(S) == source(T)        where Γ /- S = T.
Γ /-          sink(S) == sink(T)          where Γ /- S = T.
Γ /-  all(TX, S1, S2) == all(_, T1, T2)   where Γ /- S1 = T1, [TX-bName|Γ] /- S2 = T2.
Γ /- some(TX, S1, S2) == some(_, T1, T2)  where Γ /- S1 = T1, [TX-bName|Γ] /- S2 = T2.
Γ /-  abs(TX, K1, S2) == abs(_, K1, T2)   where [TX-bName | g] /- S2 = T2.
Γ /-          S1 $ S2 == T1 $ T2          where Γ /- S1 = T1, Γ /- S2 = T2.

Γ \-                T :: K                where Γ /- T :: K, !.
Γ \-                T :: K                where writeln(error : kindof(T, K)), fail.

Γ /-                X :: '*'              where val(X), \+ member(X-_, Γ).
Γ /-                X :: K                where val(X), getb(Γ, X, bTVar(T)), Γ \- T :: K, !.
Γ /-                X :: K                where val(X), !, getb(Γ, X, bTAbb(_, some(K))).
Γ /-       (T1 -> T2) :: '*'              where !, Γ \- T1 :: '*', Γ \- T2 :: '*'.
Γ /-             {Tf} :: '*'              where maplist([L : S] >> (Γ \- S :: '*'), Tf).
Γ /-      variant(Tf) :: '*'              where maplist([L : S] >> (Γ \- S :: '*'), Tf).
Γ /-           ref(T) :: '*'              where Γ \- T :: '*'.
Γ /-        source(T) :: '*'              where Γ \- T :: '*'.
Γ /-          sink(T) :: '*'              where Γ \- T :: '*'.
Γ /-  all(TX, T1, T2) :: '*'              where !, [TX-bTVar(T1) | Γ] \- T2 :: '*'.
Γ /-  abs(TX, K1, T2) :: kArr(K1, K)      where !, maketop(K1, T1), [TX-bTVar(T1) | Γ] \- T2 :: K.
Γ /-          T1 $ T2 :: K12              where !, Γ \- T1 :: kArr(K11, K12), Γ \- T2 :: K11.
Γ /- some(TX, T1, T2) :: '*'              where !, [TX-bTVar(T1) | Γ] \- T2 :: '*'.
Γ /-                T :: '*'.

promote(Γ, X, T)                          where val(X), getb(Γ, X, bTVar(T)).
promote(Γ, S $ T, S_ $ T)                 where promote(Γ, S, S_).

Γ \-                 S <: T               where Γ /- S = T.
Γ \-                 S <: T               where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ <: T_.
Γ /-                 _ <: top.
Γ /-               bot <: _.
Γ /-                 X <: T               where val(X), promote(Γ, X, S), Γ \- S <: T.
Γ /-        (S1 -> S2) <: (T1 -> T2)      where Γ \- T1 <: S1, Γ \- S2 <: T2.
Γ /-              {SF} <: {TF}            where maplist([L : T] >> (member(L : S, SF), Γ \- S <: T), TF).
Γ /-       variant(SF) <: variant(TF)     where maplist([L : S] >> (member(L : T, TF), Γ \- S <: T), SF).
Γ /-            ref(S) <: ref(T)          where Γ \- S <: T, Γ \- T <: S.
Γ /-            ref(S) <: source(T)       where Γ \- S <: T.
Γ /-         source(S) <: source(T)       where Γ \- S <: T.
Γ /-            ref(S) <: sink(T)         where Γ \- T <: S.
Γ /-           sink(S) <: sink(T)         where Γ \- T <: S.
Γ /-           T1 $ T2 <: T               where promote(Γ, T1 $ T2, S), Γ \- S <: T.
Γ /-   abs(TX, K1, S2) <: abs(_, K1, T2)  where maketop(K1, T1), [TX-bTVar(T1)|Γ] \- S2 <: T2.
Γ /-   all(TX, S1, S2) <: all(_, T1, T2)  where Γ \- S1 <: T1, Γ \- T1 <: S1, [TX-bTVar(T1)|Γ] \- S2 <: T2.
Γ /-  some(TX, S1, S2) <: some(_, T1, T2) where Γ \- S1 <: T1, Γ \- T1 <: S1, [TX-bTVar(T1)|Γ] \- S2 <: T2.

join(Γ, S, T, T)                              where Γ \- S <: T.
join(Γ, S, T, S)                              where Γ \- T <: S.
join(Γ, S, T, R)                              where simplify(Γ, S, S_), simplify(Γ, T, T_), join2(Γ, S_, T_, R).
join2(Γ, {SF}, {TF}, {UF_})                   where include([L : _] >> member(L : _, TF), SF, UF),
                                                 maplist([L : S, L : T_] >> (member(L : T, TF), join(Γ, S, T, T_)), UF, UF_).
join2(Γ, all(TX, S1, S2), all(_, T1, T2), all(TX, S1, T2_))
                                              where Γ \- S1 <: T1, Γ \- T1 <: S1, join([TX-bTVar(T1)|Γ], T1, T2, T2_).
join2(Γ, all(TX, S1, S2), all(_, T1, T2), top).
join2(Γ,(S1 -> S2), (T1 -> T2), (S_ -> T_))   where meet(Γ, S1, T1, S_), join(Γ, S2, T2, T_).
join2(Γ,    ref(S), ref(T), ref(S))           where Γ \- S <: T, Γ \- T <: S.
join2(Γ,    ref(S), ref(T), source(T_))       where join(Γ, S, T, T_).
join2(Γ, source(S), source(T), source(T_))    where join(Γ, S, T, T_).
join2(Γ,    ref(S), source(T), source(T_))    where join(Γ, S, T, T_).
join2(Γ, source(S), ref(T), source(T_))       where join(Γ, S, T, T_).
join2(Γ,   sink(S), sink(T), sink(T_))        where meet(Γ, S, T, T_).
join2(Γ,    ref(S), sink(T), sink(T_))        where meet(Γ, S, T, T_).
join2(Γ,   sink(S), ref(T), sink(T_))         where meet(Γ, S, T, T_).
join2(Γ, _, _, top).

meet(Γ, S, T, S)                              where Γ \- S <: T.
meet(Γ, S, T, T)                              where Γ \- T <: S.
meet(Γ, S, T, R)                              where simplify(Γ, S, S_), simplify(Γ, T, T_), meet2(Γ, S_, T_, R).
meet2(Γ, {SF}, {TF}, {UF_})                   where maplist([L : S, L : T_] >> (
                                                      member(L : T, TF), meet(Γ, S, T, T_) ; T_ = S
                                                    ), SF, SF_),
                                                    include([L : _] >> (\+ member(L : _, SF)), TF, TF_),
                                                    append(SF_, TF_, UF_).
meet2(Γ, all(TX, S1, S2), all(_, T1, T2), all(TX, S1, T2_))
                                              where Γ \- S1 <: T1, Γ \- T1 <: S1,
                                                    meet([TX-bTVar(T1)|Γ], T1, T2, T2_).
meet2(Γ, (S1 -> S2), (T1 -> T2), (S_ -> T_))  where join(Γ, S1, T1, S_),
                                                    meet(Γ, S2, T2, T_).
meet2(Γ, ref(S), ref(T), ref(T))              where Γ \- S <: T, Γ \- T <: S.
meet2(Γ, ref(S), ref(T), source(T_))          where meet(Γ, S, T, T_).
meet2(Γ, source(S), source(T), source(T_))    where meet(Γ, S, T, T_).
meet2(Γ, ref(S), source(T), source(T_))       where meet(Γ, S, T, T_).
meet2(Γ, source(S), ref(T), source(T_))       where meet(Γ, S, T, T_).
meet2(Γ, sink(S), sink(T), sink(T_))          where join(Γ, S, T, T_).
meet2(Γ, ref(S), sink(T), sink(T_))           where join(Γ, S, T, T_).
meet2(Γ, sink(S), ref(T), sink(T_))           where join(Γ, S, T, T_).
meet2(_, _, bot).

lcst(Γ, S, T)                           where simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T)                          where promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T).

Γ /- true                 : bool.
Γ /- false                : bool.
Γ /- if(M1, M2, M3)       : T           where Γ /- M1 : T1, Γ \- T1 <: bool,
                                              Γ /- M2 : T2, Γ /- M3 : T3, join(Γ, T2, T3, T).
Γ /- zero                 : nat.
Γ /- succ(M1)             : nat         where Γ /- M1 : T1, Γ \- T1 <: nat.
Γ /- pred(M1)             : nat         where Γ /- M1 : T1, Γ \- T1 <: nat.
Γ /- iszero(M1)           : bool        where Γ /- M1 : T1, Γ \- T1 <: nat.
Γ /- unit                 : unit.
Γ /- F1                   : float       where float(F1).
Γ /- timesfloat(M1, M2)   : float       where Γ /- M1 : T1, Γ \- T1 <: float,
                                              Γ /- M2 : T2, Γ \- T2 <: float.
Γ /- X                    : string      where string(X).
Γ /- X                    : T           where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2)   : (T1 -> T2_) where Γ \- T1 :: '*', [X-bVar(T1)|Γ] /- M2 : T2_, !.
Γ /- M1 $ M2              : T12         where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), !,
                                              Γ /- M2 : T2, Γ \- T2 <: T11.
Γ /- M1 $ M2              : bot         where !, Γ /- M1 : T1, lcst(Γ, T1, bot), Γ /- M2 : T2.
Γ /- let(X, M1, M2)       : T           where Γ /- M1 : T1, [X-bVar(T1)|Γ] /- M2 : T.
Γ /- fix(M1)              : T12         where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ \- T12 <: T11.
Γ /- inert(T)             : T.
Γ /- as(M1, T)            : T           where Γ \- T :: '*', Γ /- M1 : T1, Γ \- T1 <: T.
Γ /- {Mf}                 : {Tf}        where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf), !.
Γ /- proj(M1, L)          : T           where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- tag(Li, Mi, T)       : T           where simplify(Γ, T, variant(Tf)), member(Li : Te, Tf),
                                              Γ /- Mi : T_, Γ \- T_ <: Te.
Γ /- case(M, Cases)       : bot         where Γ /- M : T, lcst(Γ, T, bot),
                                              maplist([L = _] >> member(L : _, Tf), Cases),
                                              maplist([Li = (Xi, Mi)] >> (
                                                member(Li : Ti, Tf), [Xi-bVar(Ti)|Γ] /- Mi : Ti_), Cases).
Γ /- case(M, Cases)       : T_          where Γ /- M : T, lcst(Γ, T, variant(Tf)),
                                              maplist([L = _] >> member(L : _, Tf), Cases),
                                              maplist([Li = (Xi, Mi), Ti_] >> (
                                                member(Li : Ti, Tf), [Xi-bVar(Ti)|Γ] /- Mi : Ti_
                                              ), Cases, CaseTypes),
                                              foldl(join(Γ), bot, CaseTypes, T_).
Γ /- ref(M1)              : ref(T1)     where Γ /- M1 : T1.
Γ /- deref(M1)            : T1          where Γ /- M1 : T, lcst(Γ, T, ref(T1)).
Γ /- deref(M1)            : bot         where Γ /- M1 : T, lcst(Γ, T, bot).
Γ /- deref(M1)            : T1          where Γ /- M1 : T, lcst(Γ, T, source(T1)).
Γ /- assign(M1, M2)       : unit        where Γ /- M1 : T, lcst(Γ, T, ref(T1)), Γ /- M2 : T2, Γ \- T2 <: T1.
Γ /- assign(M1, M2)       : bot         where Γ /- M1 : T, lcst(Γ, T, bot), Γ /- M2 : _.
Γ /- assign(M1, M2)       : unit        where Γ /- M1 : T, lcst(Γ, T, sink(T1)), Γ /- M2 : T2, subtyping(Γ, T2, T1).
Γ /- loc(l)               : _           where !, fail.
Γ /- try(M1, M2)          : T           where Γ /- M1 : T1, Γ /- M2 : T2, join(Γ, T1, T2, T).
Γ /- error                : bot         where !.
Γ /- pack(T1, M2, T)      : T           where Γ \- T :: '*', simplify(Γ, T, some(Y, TBound, T2)),
                                              Γ \- T1 <: TBound, Γ /- M2 : S2,
                                              tsubst(Y, T1, T2, T2_), Γ \- S2 <: T2_.
Γ /- unpack(TX, X, M1, M2): T2          where Γ /- M1 : T1, lcst(Γ, T1, some(_, TBound, T11)),
                                              [X-bVar(T11), TX-bTVar(TBound)|Γ] /- M2 : T2.
Γ /- (fn(TX :: T1) => M2) : all(TX, T1, T2)
                                        where [TX-bTVar(T1)|Γ] /- M2 : T2, !.
Γ /- M1![T2]              : T12_        where Γ /- M1 : T1, lcst(Γ, T1, all(X, T11, T12)),
                                              Γ \- T2 <: T11, tsubst(X, T2, T12, T12_).
Γ /- M                    : _           where writeln(error : typeof(Γ, M)), fail.

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R)                            where swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R)                           where swritef(R, ' <: %w', [T]).
show_bind(Γ, bMAbb(M, none), R)                     where Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R)                  where swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T, none), R)                     where Γ \- T :: K, swritef(R, ' :: %w', [K]).
show_bind(Γ, bTAbb(T, some(K)), R)                  where swritef(R, ' :: %w', [K]).

check_bind(Γ, bName, bName).
check_bind(Γ, bTVar(K), bTVar(K)).
check_bind(Γ, bTAbb(T, none), bTAbb(T, some(K)))    where Γ \- T :: K.
check_bind(Γ, bTAbb(T, some(K)), bTAbb(T, some(K))) where Γ \- T :: K.
check_bind(Γ, bVar(T), bVar(T)).
check_bind(Γ, bMAbb(M, none), bMAbb(M, some(T)))    where Γ /- M : T.
check_bind(Γ, bMAbb(M, some(T)), bMAbb(M, some(T))) where Γ /- M : T1, Γ /- T1 = T.

check_someBind(TBody, pack(_, T12, _), bMAbb(T12, some(TBody))).
check_someBind(TBody, _, bVar(TBody)).

run(eval(M), (Γ, St), (Γ, St_))                     where !, Γ /- M : T, !, Γ/St /- M ==>> M_/St_, !,
                                                          writeln(M_ : T).
run(bind(X, Bind), (Γ, St), ([X-Bind_|Γ], St_))     where check_bind(Γ, Bind, Bind1), evalbinding(Γ, St, Bind1, Bind_, St_),
                                                          write(X), show_bind(Γ, Bind_, R), writeln(R).
run(someBind(TX, X, M), (Γ, St), ([X-B, TX-bTVar(K)|Γ], St_))
                                                    where !, Γ /- M : T, simplify(Γ, T, some(_, K, TBody)),
                                                          Γ/St /- M ==>> M_/St_, check_someBind(TBody, M_, B),
                                                          writeln(TX), write(X), write(' : '), writeln(TBody).

run(Ls)                                             where foldl(run, Ls, ([], []), _).

:- run([eval((fn(x : bot) -> x))]).
:- run([eval((fn(x : bot) -> x $ x))]).
:- run([eval((fn(x : variant([a : bool, b : bool])) -> x))]).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(r : {[x : (top -> top)]}) -> proj(r, x) $ proj(r, x)) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]})]).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval({[x = true, y = false]})]).
:- run([eval(proj({[x = true, y = false]}, x))]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval(proj({[1 = true, 2 = false]}, 1))]).
:- run([eval(if(true, {[x = true, y = false, a = false]}, {[y = false, x = {[]}, b = false]}))]).
:- run([eval(try(error, true))]).
:- run([eval(try(if(true, error, true), false))]).
:- run([eval(timesfloat(2.0, 3.14159))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval(if(error, true, false))]).
:- run([eval(error $ true)]).
:- run([eval((fn(x : bool) -> x) $ error)]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(zero))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- halt.

