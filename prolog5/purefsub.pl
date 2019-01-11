:- discontiguous((/-)/2).
:- op(1050, xfy, [=>]).
:- op(920, xfx, [==>, ==>>, <:]).
:- op(910, xfx, [/-]).
:- op(600, xfy, [::]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= top. % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:

t ::=                     % 型
      top                 % 最大の型
    | tx                  % 変数
    | (t -> t)            % 関数の型
    | (all(tx :: t) => t) % 全称型
    .
m ::=                     % 項
      x                   % 変数
    | (fn(x : t) -> m)    % ラムダ抽象
    | m $ m               % 関数適用
    | (fn(tx <: t) => m)  % 型抽象
    | m![t]               % 型適用
    .
v ::=                     % 値:
      (fn(x : t) -> m)    % ラムダ抽象
    | (fn(tx <: t) => m)  % 型抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S                                           :- tx(J).
X![(J -> S)] tsubst X                                           :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_)                       :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_,
                                                                   T2![TX, (J -> S)] tsubst2 T2_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                                      :- T![(J -> S)] tsubst T_.

J![(J -> M)] subst M                                        :- x(J).
X![(J -> M)] subst X                                        :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_)   :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                        :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(fn(TX <: T1) => M2)![(J -> M)] subst (fn(TX <: T1) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2])                         :- M1![(J -> M)] subst M1_.
A![(J -> M)] subst B                                        :- writeln(error : A![(J -> M)] subst B), fail.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_                                   :- T![(J -> M)] subst T_.

X![(J -> S)] tmsubst X                                         :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_)     :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_)                         :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(fn(TX <: T1) => M2)![(J -> S)] tmsubst (fn(TX <: T1_) => M2_) :- T1![(J -> S)] tsubst T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_])                         :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_                                    :- T![(J -> S)] tmsubst T_.

% ------------------------   EVALUATION  ------------------------

Γ /- (fn(X : T11) -> M12) $ V2 ==> R   :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_              :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2              :- Γ /- M1 ==> M1_.
Γ /- (fn(X <: _) => M11)![T2] ==> M11_ :- M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2]              :- Γ /- M1 ==> M1_. 

Γ /- M ==>> M_                         :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

promote(Γ, X, T) :- tx(X), member(X <: T, Γ).

Γ /- T1 <: T1.
Γ /- _  <: top.
Γ /- (S1 -> S2) <: (T1 -> T2)                      :- Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ /- X <: T                                        :- tx(X), promote(Γ, X, S), Γ /- S <: T.
Γ /- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2) :- Γ /- S1 <: T1, Γ /- T1 <: S1,
                                                         [TX <: T1 | Γ] /- S2 <: T2. 

% ------------------------   TYPING  ------------------------

lcst(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst(Γ, T, T). 

Γ /- X : T                                        :- x(X), !, member(X : T, Γ),!.
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_)             :- [X : T1 | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12                                :- Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)),
                                                        Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (fn(TX <: T1) => M2) : (all(TX :: T1) => T2) :- [TX <: T1 | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_                               :- Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)),
                                                        Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _                                        :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X, T)  :- format('~w : ~w\n', [X, T]).
showSub(X, T) :- format('~w <: ~w\n', [X, T]).

run(X : T, Γ, [X : T | Γ])   :- x(X), t(T), show(X, T).
run(X <: T, Γ, [X <: T | Γ]) :- tx(X), t(T), showSub(X, T).
run(M, Γ, Γ)                       :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.

run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([(fn('X' <: top) => fn(x : 'X') -> x)]). 
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([(fn('X' <: top) => fn(x : 'X') -> x)![(all('X' :: top) => 'X' -> 'X')]]). 
%lambda x:Top. x;
:- run([(fn(x : top) -> x)]). 
%(lambda x:Top. x) (lambda x:Top. x);
:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
%lambda X<:Top->Top. lambda x:X. x x;
:- run([(fn('X' <: (top -> top)) => fn(x : 'X') -> x $ x)]).
:- run([x : top, x]).
:- run(['T' <: (top -> top), x : 'T']).

:- halt.
