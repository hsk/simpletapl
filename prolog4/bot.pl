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
val(X)                                               :- X \= top, X \= bot, atom(X).
subst(J, M, J, M)                                    :- val(J).
subst(J, M, X, X)                                    :- val(X).
subst(J, M, (fn(X : T1) -> M2), (fn(X : T1) -> M2_)) :- subst2(X, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_)                      :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst2(J, J, M, S, S).
subst2(X, J, M, S, M_)                               :- subst(J, M, S, M_).
getb(Γ, X, B)                                        :- member(X - B, Γ).
gett(Γ, X, T)                                        :- getb(Γ, X, bVar(T)).
v((fn(_ : _) -> _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R        where v(V2), subst(X, V2, M12, R).
Γ /- V1 $ M2                   ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2                   ==> M1_ $ M2 where Γ /- M1        ==> M1_.
Γ /- M                         ==> > M_     where Γ /- M         ==> M1, Γ /- M1 ==> > M_.
Γ /- M                         ==> > M.

Γ \- T1         <: T2         where T1 = T2.
Γ \- _          <: top.
Γ \- bot        <: _.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ \- T1 <: S1, Γ \- S2 <: T2.
Γ /- X : T                            where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12                    where Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, Γ \- T2 <: T11.
Γ /- M1 $ M2 : bot                    where Γ /- M1 : bot, Γ /- M2 : T2.
Γ /- M : _                            where writeln(error : typeof(Γ, M)), fail.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R)              :- swritef(R, ' : %w', [T]).
run(eval(M), Γ, Γ)                    :- Γ /- M : T, !, Γ /- M ==> > M_, !, writeln(M_ : T), !.
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls)                               :- foldl(run, Ls, [], _).
                                      :- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : bot) -> x))]).
:- run([eval((fn(x : bot) -> x $ x))]).
:- run([bind(y, bVar((bot -> bot))), bind(x, bVar(bot)), eval(y $ x)]).
:- halt.
