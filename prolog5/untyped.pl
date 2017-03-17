:- style_check(-singleton).
:- op(1200, xfx, [where]).
:- op(920, xfx, ['==>', '==>>']).
:- op(910, xfx, ['/-']).
:- op(500, yfx, ['$', !, subst, subst2]).
:- op(10, xf, [/]).

term_expansion((A where B), (A :- B)).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

x ::= atom.        % 識別子:
m ::=              % 項:
      x            % 変数
    | (fn(x) -> m) % ラムダ抽象
    | m $ m        % 関数適用
    .
v ::=              % 値:
      fn(x) -> m   % ラムダ抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

            X![X -> M]  subst M              :- x(X).
            X![Y -> M]  subst X              :- x(X).
(fn(X) -> M2)![Y -> M]  subst (fn(X) -> M2_) :- M2![X, (Y -> M)] subst2 M2_.
      M1 $ M2![Y -> M]  subst (M1_ $ M2_)    :- M1![Y -> M] subst M1_, M2![Y -> M] subst M2_.
            A![Y -> M]  subst B              :- writeln(error : A![Y -> M] subst B), fail.
      M1![Y, (Y -> M)] subst2 M1.
      M1![X, (Y -> M)] subst2 M_             :- M1![Y -> M] subst M_.

% ------------------------   EVALUATION  ------------------------

Γ /- (fn(X) -> M12) $ V2 ==> R        where v(V2), M12![X -> V2] subst R.
Γ /- V1 $ M2             ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2             ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M                  ==>> M_       where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M                  ==>> M.

% ------------------------   MAIN  ------------------------

run(X/, Γ, [X - name | Γ]) :- !, writeln(X).
run(M, Γ, Γ)               :- !, m(M), !, Γ /- M ==>> M_, !, writeln(M_).
run(Ls)                    :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

:- run([ 
   %x/;
   x /,
   %x;
x]). 
%lambda x. x;
:- run([(fn(x) -> x)]). 
%(lambda x. x) (lambda x. x x);
:- run([(fn(x) -> x) $ (fn(x) -> x $ x)]). 
%(lambda z. (lambda y. y) z) (lambda x. x x); 
:- run([(fn(z) -> (fn(y) -> y) $ z) $ (fn(x) -> x $ x)]). 
%(lambda x. (lambda x. x) x) (lambda x. x x); 
:- run([(fn(x) -> (fn(x) -> x) $ x) $ (fn(x) -> x $ x)]). 
%(lambda x. (lambda x. x) x) (lambda z. z z); 
:- run([(fn(x) -> (fn(x) -> x) $ x) $ (fn(z) -> z $ z)]).

:- halt.
