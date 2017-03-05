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
val(X) :- X \= top, atom(X).
tsubst(J, S, top, top).
tsubst(J, S, J, S) :- val(J).
tsubst(J, S, X, X) :- val(X).
tsubst(J, S, (T1 -> T2), (T1_ -> T2_)) :- tsubst(J, S, T1, T1_), tsubst(J, S, T2, T2_).
tsubst(J, S, all(TX, T1, T2), all(TX, T1_, T2_)) :- tsubst2(TX, J, S, T1, T1_), tsubst2(TX, J, S, T2, T2_).
tsubst2(X, X, S, T, T).
tsubst2(X, J, S, T, T_) :- tsubst(J, S, T, T_).
subst(J, M, J, M) :- val(J).
subst(J, M, X, X) :- val(X).
subst(J, M, (fn(X1 : T1) -> M2), (fn(X1 : T1) -> M2_)) :- subst2(X1, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, (fn(TX :: T1) => M2), (fn(TX :: T1) => M2_)) :- subst(J, M, M2, M2_).
subst(J, M, M1![T2], M1_![T2]) :- subst(J, M, M1, M1_).
subst(J, M, A, B) :- writeln(error : subst(J, M, A, B)), fail.
subst2(X, X, M, T, T).
subst2(X, J, M, T, T_) :- subst(J, M, T, T_).
tmsubst(J, S, X, X) :- val(X).
tmsubst(J, S, (fn(X : T1) -> M2), (fn(X : T1_) -> M2_)) :- tsubst(J, S, T1, T1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, M1 $ M2, M1_ $ M2_) :- tmsubst(J, S, M1, M1_), tmsubst(J, S, M2, M2_).
tmsubst(J, S, (fn(TX :: T1) => M2), (fn(TX :: T1_) => M2_)) :- tsubst(J, S, T1, T1_), tmsubst2(TX, J, S, M2, M2_).
tmsubst(J, S, M1![T2], M1_![T2_]) :- tmsubst(J, S, M1, M1_), tsubst(J, S, T2, T2_).
tmsubst2(X, X, S, T, T).
tmsubst2(X, J, S, T, T_) :- tmsubst(J, S, T, T_).
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)), !.
gett(Γ, X, _) :- writeln(error : gett(Γ, X)), fail.
v((fn(_ : _) -> _)).
v((fn(_ :: _) => _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), subst(X, V2, M12, R).
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where tmsubst(X, T2, M11, M11_).
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
promote(Γ, X, T) :- val(X), getb(Γ, X, bTVar(T)).
Γ \- T1 <: T2 where T1 = T2.
Γ \- _ <: top.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ \- T1 <: S1, Γ \- S2 <: T2.
Γ \- X <: T where val(X), promote(Γ, X, S), Γ \- S <: T.
Γ \- all(TX, S1, S2) <: all(_, T1, T2) where Γ \- S1 <: T1, Γ \- T1 <: S1, [TX - bTVar(T1) | Γ] \- S2 <: T2.
lcst(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst(Γ, T, T).
Γ /- X : T where val(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ \- T2 <: T11.
Γ /- (fn(TX :: T1) => M2) : all(TX, T1, T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, all(X, T11, T12)), Γ \- T2 <: T11, tsubst(X, T2, T12, T12_).
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail.
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' <: %w', [T]).
run(eval(M), Γ, Γ) :- Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]).
:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x))![all('X', top, ('X' -> 'X'))])]).
:- run([eval((fn(x : top) -> x))]).
:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]).
:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]).
:- run([bind(x, bVar(top))]).
:- run([bind(x, bVar(top)), eval(x)]).
:- run([bind('T', bTVar((top -> top)))]).
:- run([bind('T', bTVar((top -> top))), bind(x, bVar('T'))]).
:- halt.

