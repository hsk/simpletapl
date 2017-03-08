:- style_check(-singleton).
:- op(1200, xfx, [where]).
:- op(920, xfx, ['==>', '==>>']).
:- op(910, xfx, ['/-']).
:- op(500, yfx, ['$', !, subst, subst2]).

term_expansion((A where B), (A :- B)).


% 構文

x(X) :- atom(X).                          % 識別子

m(M) :-                                   % 項:
        M = X, x(X)                       % 変数
      ; M = (fn(X) -> M1), x(X), m(M1)    % ラムダ抽象
      ; M = M1 $ M2, m(M1), m(M2)         % 関数適用
      .
v(V) :-                                   % 値:
        V = (fn(X) -> M1), x(X), m(M1)    % ラムダ抽象値
      .

% 置換

            X![X -> M]  subst M              :- x(X).
            X![Y -> M]  subst X              :- x(X).
(fn(X) -> M2)![Y -> M]  subst (fn(X) -> M2_) :- M2![X, (Y -> M)] subst2 M2_.
      M1 $ M2![Y -> M]  subst (M1_ $ M2_)    :- M1![Y -> M] subst M1_, M2![Y -> M] subst M2_.
            A![Y -> M]  subst B              :- writeln(error : A![Y -> M] subst B), fail.
      M1![Y, (Y -> M)] subst2 M1.
      M1![X, (Y -> M)] subst2 M_             :- M1![Y -> M] subst M_.

% 評価 M ==> M_

Γ /- (fn(X) -> M12) $ V2 ==> R        where v(V2), M12![X -> V2] subst R.
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

