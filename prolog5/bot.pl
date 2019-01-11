:- discontiguous((/-)/2).
:- op(1200, xfx, [--]).
:- op(920, xfx, [==>, ==>*, <:]).
:- op(910, xfx, [/-]).
:- op(500, yfx, [$, !, subst, subst2]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= top | bot.                     % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X). % 識別子:

t ::=                                % 型:
    (t -> t)                         % 関数の型
    | top                            % 最大の型
    | bot                            % 最小の型
    .
m ::=                                % 項:
    x                                % 変数
    | (fn(x:t) -> m)                 % ラムダ抽象
    | m $ m                          % 関数適用
    .
v ::=                                % 値:
      fn(x:t) -> m                   % ラムダ抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

J![(J -> M)] subst M                                :- x(J).
X![(J -> M)] subst X                                :- x(X).
(fn(X:T1) -> M2)![(J -> M)] subst (fn(X:T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                           :- S![(J -> M)] subst M_.

% ------------------------   EVALUATION  ------------------------

(fn(X:T11) -> M12) $ V2 ==> R :- v(V2), M12![(X -> V2)] subst R.
V1 $ M2 ==> V1 $ M2_          :- v(V1), M2 ==> M2_.
M1 $ M2 ==> M1_ $ M2          :- M1 ==> M1_.

M ==>* M_                     :- M ==> M1, M1 ==>* M_.
M ==>* M. 

% ------------------------   SUBTYPING  ------------------------

T1  <: T1.
_   <: top.
bot <: _.
(S1 -> S2) <: (T1 -> T2) :- T1 <: S1, S2 <: T2. 

% ------------------------   TYPING  ------------------------

Γ /- X:T                          :- x(X), !, member(X:T, Γ).
Γ /- (fn(X:T1) -> M2):(T1 -> T2_) :- [X:T1 | Γ] /- M2:T2_, !.
Γ /- M1 $ M2:T12                  :- Γ /- M1:(T11 -> T12), Γ /- M2:T2, T2 <: T11.
Γ /- M1 $ M2:bot                  :- Γ /- M1:bot, Γ /- M2:T2.
Γ /- M:_                          :- writeln(error:typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X, T)           :- format('~w:~w\n', [X, T]).
run(X:T, Γ, [X:T|Γ]) :- show(X, T).
run(M, Γ, Γ)         :- m(M), !, Γ /- M:T, !, M ==>* M_, !, writeln(M_:T).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

:- run([(fn(x:top) -> x)]). 
:- run([(fn(x:top) -> x) $ (fn(x:top) -> x)]). 
:- run([(fn(x:(top -> top)) -> x) $ (fn(x:top) -> x)]). 
:- run([(fn(x:bot) -> x)]). 
:- run([(fn(x:bot) -> x $ x)]). 
:- run([y:(bot -> bot), x:bot, y $ x]).

:- halt.
