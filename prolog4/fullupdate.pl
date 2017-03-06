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
val(X) :- X \= bool, X \= nat, X \= unit, X \= float, X \= string, X \= top, X \= true, X \= false, X \= zero, atom(X).
tsubst(J, S, bool, bool).
tsubst(J, S, nat, nat).
tsubst(J, S, unit, unit).
tsubst(J, S, float, float).
tsubst(J, S, string, string).
tsubst(J, S, top, top).
tsubst(J, S, J, S) :- val(J).
tsubst(J, S, X, X) :- val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_)) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, {Mf}, {Mf_}) :- maplist([L : (Vari, T), L : (Vari, T_)] >> tsubst(J, S, T, T_), Mf, Mf_).
tsubst(J, S, all(TX, T1, T2), all(TX, T1_, T2_)) :- tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, some(TX, T1, T2), some(TX, T1_, T2_)) :- tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, abs(TX, K, T2), abs(TX, K, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, T1 $ T2, T1_ $ T2_) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
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
subst(J, M, {Mf}, {Mf_}) :- maplist([L = (Vari, Mi), L = (Vari, Mi_)] >> subst(J, M, Mi, Mi_), Mf, Mf_).
subst(J, M, proj(M1, L), proj(M1_, L)) :- subst(J, M, M1, M1_).
subst(J, M, (fn(TX :: T) => M2), (fn(TX :: T) => M2_)) :- subst(J, M, M2, M2_).
subst(J, M, M1![T2], M1_![T2]) :- subst(J, M, M1, M1_).
subst(J, M, pack(T1, M2, T3), pack(T1, M2_, T3)) :- subst(J, M, M2, M2_).
subst(J, M, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) :- subst2(X, J, M, M1, M1_), subst2(X, J, M, M2, M2_).
subst(J, M, update(M1, L, M2), update(M1_, L, M2_)) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
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
tmsubst(J, M, unit, unit).
tmsubst(J, M, F1, F1) :- float(F1).
tmsubst(J, M, timesfloat(M1, M2), timesfloat(M1_, M2_)) :- tmsubst(J, M, M1, M1_), tmsubst(J, M, M2, M2_).
tmsubst(J, M, X, X) :- string(X).
tmsubst(J, S, X, X) :- val(X).
tmsubst(J, S, (fn(X : T1) -> M2), (fn(X : T1_) -> M2_)) :- tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, M1 $ M2, M1_ $ M2_) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, let(X, M1, M2), let(X, M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, M, fix(M1), fix(M1_)) :- tmsubst(J, M, M1, M1_).
tmsubst(J, M, inert(T1), inert(T1)).
tmsubst(J, S, as(M1, T1), as(M1_, T1_)) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T1, T1_).
tmsubst(J, M, {Mf}, {Mf_}) :- maplist([L = (Vari, Mi), L = (Vari, Mi_)] >> tmsubst(J, M, Mi, Mi_), Mf, Mf_).
tmsubst(J, M, proj(M1, L), proj(M1_, L)) :- tmsubst(J, M, M1, M1_).
tmsubst(J, S, (fn(TX :: T1) => M2), (fn(TX :: T1_) => M2_)) :- tsubst2(TX, J, S, T1, T1_), tmsubst2(TX, J, S, M2, M2_).
tmsubst(J, S, M1![T2], M1_![T2_]) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T2, T2_).
tmsubst(J, S, pack(T1, M2, T3), pack(T1_, M2_, T3_)) :- tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_), tsubst(J, S, T3, T3_).
tmsubst(J, S, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, update(M1, L, M2), update(M1_, L, M2_)) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst2(X, X, S, T, T).
tmsubst2(X, J, S, T, T_) :- tmsubst(J, S, T, T_).
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))).
maketop('*', top).
maketop(kArr(K1, K2), abs('_', K1, K2_)) :- maketop(K2, K2_).
n(zero).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
v(unit).
v(F1) :- float(F1).
v(X) :- string(X).
v((fn(_ : _) -> _)).
v({Mf}) :- maplist([L = (_, M)] >> v(M), Mf).
v(pack(_, V1, _)) :- v(V1).
v((fn(_ :: _) => _)).
e([L = (Vari, M) | Mf], M, [L = (Vari, M_) | Mf], M_) :- \+ v(M).
e([L = (Vari, M) | Mf], M1, [L = (Vari, M) | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
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
Γ /- timesfloat(F1, F2) ==> F3 where float(F1), float(F2), F3 is F1 * F2.
Γ /- timesfloat(V1, M2) ==> timesfloat(V1, M2_) where v(V1), Γ /- M2 ==> M2_.
Γ /- timesfloat(M1, M2) ==> timesfloat(M1_, M2) where Γ /- M1 ==> M1_.
Γ /- X ==> M where val(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : _) -> M12) $ V2 ==> R where v(V2), subst(X, V2, M12, R).
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- let(X, V1, M2) ==> M2_ where v(V1), subst(X, V1, M2, M2_).
Γ /- let(X, M1, M2) ==> let(X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_ where subst(X, fix((fn(X : T) -> M12)), M12, M12_).
Γ /- fix(M1) ==> fix(M1_) where Γ /- M1 ==> M1_.
Γ /- as(V1, _) ==> V1 where v(V1).
Γ /- as(M1, T) ==> as(M1_, T) where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- proj({Mf}, L) ==> M where v({Mf}), member(L = (_, M), Mf).
Γ /- proj(M1, L) ==> proj(M1_, L) where Γ /- M1 ==> M1_.
Γ /- pack(T1, M2, T3) ==> pack(T1, M2_, T3) where Γ /- M2 ==> M2_.
Γ /- unpack(_, X, pack(T11, V12, _), M2) ==> M where v(V12), subst(X, V12, M2, M2_), tmsubst(X, T11, M2_, M).
Γ /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- update({Mf}, L, V2) ==> {Mf_} where v({Mf}), v(V2), maplist([ML = (Var, M), ML = (Var, R)] >> (ML = L, R = V2 ; R = M), Mf, Mf_).
Γ /- update(V1, L, M2) ==> update(V1, L, M2_) where v(V1), Γ /- M2 ==> M2_.
Γ /- update(M1, L, M2) ==> update(M1_, L, M2) where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where tmsubst(X, T2, M11, M11_).
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
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
Γ /- top == top.
Γ /- X == T :- val(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- val(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : (TVar, T)] >> (member(L : (TVar, S), Sf), Γ /- S = T), Tf).
Γ /- all(TX, S1, S2) == all(_, T1, T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- some(TX, S1, S2) == some(_, T1, T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- abs(TX, K1, S2) == abs(_, K1, T2) :- [TX - bName | g] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ \- T :: K where Γ /- T :: K, !.
Γ \- T :: K where writeln(error : kindof(T, K)), fail.
Γ /- X :: '*' where val(X), \+ member(X - _, Γ).
Γ /- X :: K where val(X), getb(Γ, X, bTVar(T)), Γ \- T :: K, !.
Γ /- X :: K where val(X), !, getb(Γ, X, bTAbb(_, some(K))).
Γ /- (T1 -> T2) :: '*' where !, Γ \- T1 :: '*', Γ \- T2 :: '*'.
Γ /- {Tf} :: '*' where maplist([L : (_, S)] >> (Γ \- S :: '*'), Tf).
Γ /- all(TX, T1, T2) :: '*' where !, [TX - bTVar(T1) | Γ] \- T2 :: '*'.
Γ /- abs(TX, K1, T2) :: kArr(K1, K) where !, maketop(K1, T1), [TX - bTVar(T1) | Γ] \- T2 :: K.
Γ /- T1 $ T2 :: K12 where !, Γ \- T1 :: kArr(K11, K12), Γ \- T2 :: K11.
Γ /- some(TX, T1, T2) :: '*' where !, [TX - bTVar(T1) | Γ] \- T2 :: '*'.
Γ /- T :: '*'.
promote(Γ, X, T) :- val(X), getb(Γ, X, bTVar(T)).
promote(Γ, S $ T, S_ $ T) :- promote(Γ, S, S_).
Γ \- S <: T where Γ /- S = T.
Γ \- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ <: T_.
Γ /- _ <: top.
Γ /- X <: T where val(X), promote(Γ, X, S), Γ \- S <: T.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ \- T1 <: S1, Γ \- S2 <: T2.
Γ /- {SF} <: {TF} where maplist([L : (Vart, T)] >> (member(L : (Vars, S), SF), ((Vars = invariant ; Vart = covariant), Γ \- S <: T)), TF).
Γ /- T1 $ T2 <: T where promote(Γ, T1 $ T2, S), Γ \- S <: T.
Γ /- abs(TX, K1, S2) <: abs(_, K1, T2) where maketop(K1, T1), [TX - bTVar(T1) | Γ] \- S2 <: T2.
Γ /- all(TX, S1, S2) <: all(_, T1, T2) where Γ \- S1 <: T1, Γ \- T1 <: S1, [TX - bTVar(T1) | Γ] \- S2 <: T2.
Γ /- some(TX, S1, S2) <: some(_, T1, T2) where Γ \- S1 <: T1, Γ \- T1 <: S1, [TX - bTVar(T1) | Γ] \- S2 <: T2.
join(Γ, S, T, T) :- Γ \- S <: T.
join(Γ, S, T, S) :- Γ \- T <: S.
join(Γ, S, T, R) :- simplify(Γ, S, S_), simplify(Γ, T, T_), join2(Γ, S_, T_, R).
join2(Γ, {SF}, {TF}, {UF_}) :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : (SVar, S), L : (Var, T_)] >> (member(L : (TVar, T), TF), ((SVar = TVar, Var = SVar ; Var = invariant), join(Γ, S, T, T_))), UF, UF_).
join2(Γ, all(TX, S1, S2), all(_, T1, T2), all(TX, S1, T2_)) :- Γ \- S1 <: T1, Γ \- T1 <: S1, join([TX - bTVar(T1) | Γ], T1, T2, T2_).
join2(Γ, all(TX, S1, S2), all(_, T1, T2), top).
join2(Γ, (S1 -> S2), (T1 -> T2), (S_ -> T_)) :- meet(Γ, S1, T1, S_), join(Γ, S2, T2, T_).
join2(Γ, _, _, top).
meet(Γ, S, T, S) :- Γ \- S <: T.
meet(Γ, S, T, T) :- Γ \- T <: S.
meet(Γ, S, T, R) :- simplify(Γ, S, S_), simplify(Γ, T, T_), meet2(Γ, S_, T_, R).
meet2(Γ, {SF}, {TF}, {UF_}) :- maplist([L : (SVar, S), L : (Var, T_)] >> (member(L : (TVar, T), TF), (SVar = TVar, Var = SVar ; Var = covariant), meet(Γ, S, T, T_) ; T_ = S), SF, SF_), include([L : _] >> (\+ member(L : _, SF)), TF, TF_), append(SF_, TF_, UF_).
meet2(Γ, all(TX, S1, S2), all(_, T1, T2), all(TX, S1, T2_)) :- Γ \- S1 <: T1, Γ \- T1 <: S1, meet([TX - bTVar(T1) | Γ], T1, T2, T2_).
meet2(Γ, (S1 -> S2), (T1 -> T2), (S_ -> T_)) :- join(Γ, S1, T1, S_), meet(Γ, S2, T2, T_).
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
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ \- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ \- T2 <: T11.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ \- T12 <: T11.
Γ /- inert(T) : T.
Γ /- as(M1, T) : T where Γ \- T :: '*', Γ /- M1 : T1, Γ \- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = (Var, M), L : (Var, T)] >> (Γ /- M : T), Mf, Tf), !.
Γ /- proj(M1, L) : T where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : (_, T), Tf).
Γ /- update(M1, L, M2) : T1 where Γ /- M1 : T1, Γ /- M2 : T2, lcst(Γ, T1, {Tf}), member(L : (invariant, T), Tf), Γ \- T2 <: T.
Γ /- pack(T1, M2, T) : T where Γ \- T :: '*', simplify(Γ, T, some(Y, TBound, T2)), Γ \- T1 <: TBound, Γ /- M2 : S2, tsubst(Y, T1, T2, T2_), Γ \- S2 <: T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, lcst(Γ, T1, some(_, TBound, T11)), [X - bVar(T11), TX - bTVar(TBound) | Γ] /- M2 : T2.
Γ /- (fn(TX :: T1) => M2) : all(TX, T1, T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, all(X, T11, T12)), Γ \- T2 <: T11, tsubst(X, T2, T12, T12_).
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' <: %w', [T]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T, none), R) :- Γ \- T :: K, swritef(R, ' :: %w', [K]).
show_bind(Γ, bTAbb(T, some(K)), R) :- swritef(R, ' :: %w', [K]).
run(eval(M), Γ, Γ) :- !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- check_bind(Γ, Bind, Bind1), evalbinding(Γ, Bind1, Bind_), write(X), show_bind(Γ, Bind_, R), writeln(R).
run(someBind(TX, X, M), Γ, [X - B, TX - bTVar(TBound) | Γ]) :- !, Γ /- M : T, lcst(Γ, T, some(_, TBound, TBody)), Γ /- M ==>> M_, check_someBind(TBody, M_, B), writeln(TX), write(X), write(' : '), writeln(TBody).
check_bind(Γ, bName, bName).
check_bind(Γ, bTVar(S), bTVar(S)) :- Γ \- S :: _.
check_bind(Γ, bTAbb(T, none), bTAbb(T, some(K))) :- Γ \- T :: K.
check_bind(Γ, bTAbb(T, some(K)), bTAbb(T, some(K))) :- Γ \- T :: K.
check_bind(Γ, bVar(T), bVar(T)).
check_bind(Γ, bMAbb(M, none), bMAbb(M, some(T))) :- Γ /- M : T.
check_bind(Γ, bMAbb(M, some(T)), bMAbb(M, some(T))) :- Γ /- M : T1, Γ \- T1 <: T.
check_someBind(TBody, pack(_, T12, _), bMAbb(T12, some(TBody))).
check_someBind(TBody, _, bVar(TBody)).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(r : {[x : (covariant, (top -> top))]}) -> proj(r, x) $ proj(r, x)) $ {[x = (covariant, (fn(z : top) -> z)), y = (covariant, (fn(z : top) -> z))]})]).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval(let(x, true, x))]).
:- run([eval({[x = (covariant, true), y = (covariant, false)]})]).
:- run([eval(proj({[x = (covariant, true), y = (covariant, false)]}, x))]).
:- run([eval({[1 = (covariant, true), 2 = (covariant, false)]})]).
:- run([eval(proj({[1 = (covariant, true), 2 = (covariant, false)]}, 1))]).
:- run([eval(if(true, {[x = (covariant, true), y = (covariant, false), a = (covariant, false)]}, {[y = (covariant, false), x = (covariant, {[]}), b = (covariant, false)]}))]).
:- run([eval(timesfloat(2.0, 3.14159))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x))![all('X', top, ('X' -> 'X'))])]).
:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(zero))]).
:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval(pack(all('Y', top, 'Y'), (fn(x : all('Y', top, 'Y')) -> x), some('X', top, ('X' -> 'X'))))]).
:- run([eval(pack(nat, {[c = (covariant, zero), f = (covariant, (fn(x : nat) -> succ(x)))]}, some('X', top, {[c : (covariant, 'X'), f : (covariant, ('X' -> nat))]})))]).
:- halt.
