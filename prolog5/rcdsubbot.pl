:- discontiguous((/-)/2).
:- op(920, xfx, [==>, ==>>, <:]).
:- op(910, xfx, [/-]).
:- op(500, yfx, [$, !, subst, subst2]).
:- op(400, yfx, [#]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= top | bot.                          % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X).      % 識別子:
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A | list(A)].           % リスト

t ::=                  % 型:
      top              % 最大の型
    | bot              % 最小の型
    | (t -> t)         % 関数の型
    | {list(l : t)}    % レコードの型
    .
m ::=                  % 項:
      x                % 変数
    | (fn(x : t) -> m) % ラムダ抽象
    | m $ m            % 関数適用
    | {list(l = m)}    % レコード
    | m # l            % 射影
    .
v ::=                  % 値:
      (fn(x : t) -> m) % ラムダ抽象
    | {list(l = v)}    % レコード
    . 

% ------------------------   SUBSTITUTION  ------------------------

J![(J -> M)] subst M                                    :- x(J).
X![(J -> M)] subst X                                    :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                    :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
{Mf}![(J -> M)] subst {Mf_}                             :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L                         :- M1![(J -> M)] subst M1_.
A![(X -> M)] subst B                                    :- writeln(error : A![(X -> M)] subst B), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                               :- S![(J -> M)] subst M_.

% ------------------------   EVALUATION  ------------------------

e([L = M | Mf], M, [L = M_ | Mf], M_)  :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

Γ /- (fn(X : T11) -> M12) $ V2 ==> R :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_            :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2            :- Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_}                  :- e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M                  :- member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L              :- Γ /- M1 ==> M1_.
Γ /- M ==>> M_                       :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

T1  <: T1.
_   <: top.
bot <: _.
(S1 -> S2) <: (T1 -> T2) :- T1 <: S1, S2 <: T2.
{SF} <: {TF}             :- maplist([L : T] >> (member(L : S, SF), S <: T), TF). 

% ------------------------   TYPING  ------------------------

Γ /- X : T                            :- x(X), !, member(X : T, Γ).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- [X : T1 | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, T2 <: T11.
Γ /- M1 $ M2 : bot                    :- Γ /- M1 : bot, Γ /- M2 : T2.
Γ /- {Mf} : {Tf}                      :- maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : bot                     :- Γ /- M1 : bot.
Γ /- M1 # L : T                       :- Γ /- M1 : {Tf}, member(L : T, Tf).
Γ /- M : _                            :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X, T)              :- format('~w : ~w\n', [X, T]).
run(X : T, Γ, [X : T | Γ]) :- x(X), t(T), !, show(X, T).
run(M, Γ, Γ)               :- m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(Ls)                    :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

:- run([(fn(x : top) -> x)]). 
:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
:- run([(fn(r : {[x : (top -> top)]}) -> r # x $ r # x)]). 
:- run([{[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]}]). 
:- run([(fn(x : bot) -> x)]). 
:- run([(fn(x : bot) -> x $ x)]).
:- run([x : top, y : bot, {[1 = x, 2 = y]}]).

:- halt.
