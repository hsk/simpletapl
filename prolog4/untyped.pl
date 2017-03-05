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
subst(J, M, J, M) :- val(J).
subst(J, M, X, X) :- val(X).
subst(J, M, fn(X, M2), fn(X, M2_)) :- subst2(X, J, M, M2, M2_).
subst(J, M, M1 $ M2, M1_ $ M2_) :- subst(J, M, M1, M1_), subst(J, M, M2, M2_).
subst(J, M, A, B) :- writeln(error : subst(J, M, A, B)), fail.
subst2(J, J, M, S, S).
subst2(X, J, M, S, M_) :- subst(J, M, S, M_).
getb(Γ, X, B) :- member(X - B, Γ).
v(fn(_, _)).
Γ /- fn(X, M12) $ V2 ==> R where v(V2), subst(X, V2, M12, R).
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
run(eval(M), Γ, Γ) :- !, Γ /- M ==>> M_, !, writeln(M_).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- !, writeln(X).
run(Ls) :- foldl(run, Ls, [], _).
:- run([bind(x, bName), eval(x), eval(fn(x, x)), eval(fn(x, x) $ fn(x, x $ x)), eval(fn(z, fn(y, y) $ z) $ fn(x, x $ x)), eval(fn(x, fn(x, x) $ x) $ fn(x, x $ x)), eval(fn(x, fn(x, x) $ x) $ fn(z, z $ z))]).
:- halt.

