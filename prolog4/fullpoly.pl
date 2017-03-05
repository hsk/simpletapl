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
tsubst(J, S, some(TX, T2), some(TX, T2_)) :- tsubst2(TX, J, S, T2, T2_).
tsubst(J, S, all(TX, T2), all(TX, T2_)) :- tsubst2(TX, J, S, T2, T2_).
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
subst(J, M, pack(T1, M2, T3), pack(T1, M2_, T3)) :- subst(J, M, M2, M2_).
subst(J, M, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) :- subst2(X, J, M, M1, M1_), subst2(X, J, M, M2, M2_).
subst(J, M, (fn(TX) => M2), (fn(TX) => M2_)) :- subst(J, M, M2, M2_).
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
tmsubst(J, M, {Mf}, {Mf_}) :- maplist([L = Mi, L = Mi_] >> tmsubst(J, M, Mi, Mi_), Mf, Mf_).
tmsubst(J, M, proj(M1, L), proj(M1_, L)) :- tmsubst(J, M, M1, M1_).
tmsubst(J, M, pack(T1, M2, T3), pack(T1_, M2_, T3_)) :- tsubst(J, S, T1, T1_), tmsubst(J, M, M2, M2_), tsubst(J, S, T3, T3_).
tmsubst(J, M, unpack(TX, X, M1, M2), unpack(TX, X, M1_, M2_)) :- tmsubst2(TX, J, M, M1, M1_), tmsubst2(TX, J, M, M2, M2_).
tmsubst(J, S, (fn(TX) => M2), (fn(TX) => M2_)) :- tmsubst2(TX, J, S, M2, M2_).
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
v(pack(_, V1, _)) :- v(V1).
v((fn(_) => _)).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
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
Γ /- proj({Mf}, L) ==> M where member(L = M, Mf).
Γ /- proj(M1, L) ==> proj(M1_, L) where Γ /- M1 ==> M1_.
Γ /- pack(T1, M2, T3) ==> pack(T1, M2_, T3) where Γ /- M2 ==> M2_.
Γ /- unpack(_, X, pack(T11, V12, _), M2) ==> M where v(V12), subst(X, V12, M2, M2_), tmsubst(X, T11, M2_, M).
Γ /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- (fn(X) => M11)![T2] ==> M11_ where tmsubst(X, T2, M11, M11_).
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
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
Γ /- X == T :- val(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- val(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- val(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- all(TX1, S2) == all(_, T2) :- [TX1 - bName | Γ] /- S2 = T2.
Γ /- some(TX1, S2) == some(_, T2) :- [TX1 - bName | Γ] /- S2 = T2.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- zero : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- timesfloat(M1, M2) : float where Γ /- M1 : T1, Γ /- T1 = float, Γ /- M2 : T2, Γ /- T2 = float.
Γ /- X : string where string(X).
Γ /- X : T where val(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- let(X, M1, M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- as(M1, T) : T where Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- proj(M1, L) : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- pack(T1, M2, T) : T where simplify(Γ, T, some(Y, T2)), Γ /- M2 : S2, tsubst(Y, T1, T2, T2_), Γ /- S2 = T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, simplify(Γ, T1, some(_, T11)), [X - bVar(T11), TX - bTVar | Γ] /- M2 : T2.
Γ /- (fn(TX) => M2) : all(TX, T2) where [TX - bTVar | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, simplify(Γ, T1, all(X, T12)), tsubst(X, T2, T12, T12_).
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar, '').
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), Γ, Γ) :- !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, bMAbb(M, none)), Γ, [X - Bind | Γ]) :- Γ /- M : T, evalbinding(Γ, bMAbb(M, some(T)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S).
run(bind(X, bMAbb(M, some(T))), Γ, [X - Bind | Γ]) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, bMAbb(M, some(T)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S).
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(someBind(TX, X, M), Γ, [X - bMAbb(T12, some(TBody)), TX - bTVar | Γ]) :- Γ /- M : T, simplify(Γ, T, some(_, TBody)), Γ /- M ==>> pack(_, T12, _), writeln(TX), write(X), write(' : '), writeln(TBody).
run(someBind(TX, X, M), Γ, [X - bVar(TBody), TX - bTVar | Γ]) :- Γ /- M : T, simplify(Γ, T, some(_, TBody)), writeln(TX), write(X), write(' : '), writeln(TBody).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval("hello")]).
:- run([eval(unit)]).
:- run([eval((fn(x : 'A') -> x))]).
:- run([eval(let(x, true, x))]).
:- run([eval(timesfloat(2.0, 3.14159))]).
:- run([eval((fn(x : bool) -> x))]).
:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- run([eval((fn(x : nat) -> succ(x)))]).
:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(zero))]).
:- run([bind('T', bTAbb((nat -> nat))), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]).
:- run([eval((fn('X') => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X') => (fn(x : 'X') -> x))![all('X', ('X' -> 'X'))])]).
:- run([eval(pack(nat, (fn(x : nat) -> succ(x)), some('X', ('X' -> nat))))]).
:- run([eval(pack(all('Y', 'Y'), (fn(x : all('Y', 'Y')) -> x), some('X', ('X' -> 'X'))))]).
:- run([eval({[x = true, y = false]})]).
:- run([eval(proj({[x = true, y = false]}, x))]).
:- run([eval({[1 = true, 2 = false]})]).
:- run([eval(proj({[1 = true, 2 = false]}, 1))]).
:- run([eval(pack(nat, {[c = zero, f = (fn(x : nat) -> succ(x))]}, some('X', {[c : 'X', f : ('X' -> nat)]})))]).
:- run([eval(unpack('X', ops, pack(nat, {[c = zero, f = (fn(x : nat) -> succ(x))]}, some('X', {[c : 'X', f : ('X' -> nat)]})), proj(ops, f) $ proj(ops, c)))]).
:- halt.

