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

val(X) :- atom(X).

tsubst(J, S, J, S)                                     :- val(J).
tsubst(J, S, X, X)                                     :- val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_))                 :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, rec(X, T1), rec(X, T1_))                  :- tsubst2(X, J, S, T1, T1_).
tsubst2(X, X, S, T, T).
tsubst2(X, J, S, T, T_)                                :- tsubst(J, S, T, T_).
subst(J, M, J, M)                                      :- val(J).
subst(J, M, X, X)                                      :- val(X).
subst(J, M, (fn(X1 : T1) -> M2), (fn(X1 : T1) -> M2_)) :- subst2(X1, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_)                        :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst2(J, J, M, S, S).
subst2(X, J, M, S, M_)                                 :- subst(J, M, S, M_).
getb(Γ, X, B)                                          :- member(X - B, Γ).
gett(Γ, X, T)                                          :- getb(Γ, X, bVar(T)).
v((fn(_ : _) -> _)).

Γ /- fn(X, M12) $ V2     ==> R        where v(V2), subst(X, V2, M12, R).
Γ /- V1 $ M2             ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2             ==> M1_ $ M2 where Γ /- M1        ==> M1_.
Γ /- M                   ==>> M_      where Γ /- M         ==> M1, Γ /- M1 ==>> M_.
Γ /- M                   ==>> M.

compute(Γ, rec(X, S1), T)            :- tsubst(X, rec(X, S1), S1, T).
simplify(Γ, T, T_)                   :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T                           :- teq([], Γ, S, T).
teq(Seen, Γ, S, T)                   :- member((S, T), Seen).
teq(Seen, Γ, X, Y)                   :- val(X), val(Y).
teq(Seen, Γ, (S1 -> S2), (T1 -> T2)) :- teq(Seen, Γ, S1, T1), teq(Seen, Γ, S2, T2).
teq(Seen, Γ, rec(X, S1), T)          :- S = rec(X, S1), tsubst(X, S, S1, S1_), teq([(S, T) | Seen], Γ, S1_, T).
teq(Seen, Γ, S, rec(X, T1))          :- T = rec(X, T1), tsubst(X, T, T1, T1_), teq([(S, T) | Seen], Γ, S, T1_).

Γ /- X : T                            where val(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                    where Γ /- M1 : T1, Γ /- M2 : T2, simplify(Γ, T1, (T11 -> T12)), Γ /- T2 = T11.

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R)              :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar, '').

run(eval(M), Γ, Γ)                    :- !, Γ /- M : T, !, Γ /- M ==> > M_, !, writeln(M_ : T).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls)                               :- foldl(run, Ls, [], _).

:- run([eval((fn(x : 'A') -> x))]).
:- run([eval((fn(f : rec('X', ('A' -> 'A'))) -> (fn(x : 'A') -> f $ x)))]).
:- run([eval((fn(x : 'T') -> x))]).
:- run([bind('T', bTVar), bind(i, bVar('T')), eval(i)]).
:- halt.

