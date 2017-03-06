:- style_check(-singleton).
:- op(1200, xfx, [where]).
:- op(920, xfx, ['==>', '==>>']).
:- op(910, xfx, ['/-']).
:- op(500, yfx, ['$', !, subst, subst2]).

term_expansion((A where B), (A :- B)).

val(X) :- atom(X).

% 構文

m(M) :-                                   % 項
        M = X, val(X)                     % 変数
      ; M = (fn(X) -> M1), val(X), m(M1)  % ラムダ抽象
      ; M = M1 $ M2, m(M1), m(M2)         % 関数適用
      .
v(V) :-                                   % 値:
        V = (fn(X) -> M1), val(X), m(M1)  % ラムダ抽象値
      .

% 置換

J![(J -> M)]             subst M              :- val(J).
X![(J -> M)]             subst X              :- val(X).
(fn(X) -> M2)![(J -> M)] subst (fn(X) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)]       subst (M1_ $ M2_)    :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
A![(J -> M)]             subst B              :- writeln(error : A![(J -> M)] subst B), fail.
S![J, (J -> M)]         subst2 S.
S![X, (J -> M)]         subst2 M_             :- S![(J -> M)] subst M_.

getb(Γ, X, B) :- member(X - B, Γ).

% 評価 M ==> M_

Γ /- (fn(X) -> M12) $ V2 ==> R        where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2             ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2             ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M                  ==>> M_       where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M                  ==>> M.

run(eval(M), Γ, Γ)                    :- !, m(M), !, Γ /- M ==>> M_, !, writeln(M_).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- !, writeln(X).
run(Ls)                               :- foldl(run, Ls, [], _).

:- run([bind(x, bName),
        eval(x),
        eval((fn(x) -> x)),
        eval((fn(x) -> x) $ (fn(x) -> x $ x)),
        eval((fn(z) -> (fn(y) -> y) $ z) $ (fn(x) -> x $ x)),
        eval((fn(x) -> (fn(x) -> x) $ x) $ (fn(x) -> x $ x)),
        eval((fn(x) -> (fn(x) -> x) $ x) $ (fn(z) -> z $ z))]).
:- halt.

