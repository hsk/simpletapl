:- discontiguous((/-)/2).
:- op(920, xfx, [==>, ==>>, <:]).
:- op(910, xfx, [/-]).
:- op(500, yfx, [$, !, subst, subst2]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | true | false. % キーワード:

syntax(x). x(X) :- \+ w(X), atom(X), sub_atom(X, 0, 1, _, P), (char_type(P, lower) ; P = '_').  % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:

t ::=                  % 型:
      bool             % ブール値型
    | nat              % 自然数型
    | tx               % 型変数
    | (t -> t)         % 関数の型
    .
m ::=                  % 項:
      true             % 真
    | false            % 偽
    | if(m, m, m)      % 条件式
    | 0                % ゼロ
    | succ(m)          % 後者値
    | pred(m)          % 前者値
    | iszero(m)        % ゼロ判定
    | x                % 変数
    | (fn(x : t) -> m) % ラムダ抽象
    | m $ m            % 関数適用
    .
n ::=                  % 数値:
      0                % ゼロ
    | succ(n)          % 後者値
    .
v ::=                  % 値:
      true             % 真
    | false            % 偽
    | n                % 数値
    | (fn(x : t) -> m) % ラムダ抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_)         :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_,
                                                             M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_)                       :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_)                       :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_)                   :- M1![(J -> M)] subst M1_.
J![(J -> M)] subst M                                      :- x(J).
X![(J -> M)] subst X                                      :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                      :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_. 
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_                                 :- T![(J -> M)] subst T_.

% ------------------------   EVALUATION  ------------------------

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) :- Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_)             :- Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1              :- n(N1).
Γ /- pred(M1) ==> pred(M1_)             :- Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false         :- n(N1).
Γ /- iszero(M1) ==> iszero(M1_)         :- Γ /- M1 ==> M1_.
Γ /- (fn(X : T11) -> M12) $ V2 ==> R    :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_               :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2               :- Γ /- M1 ==> M1_. 

Γ /- M ==>> M_ :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   TYPING  ------------------------

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2              :- Γ /- M1 : bool, Γ /- M2 : T2, Γ /- M3 : T2.
Γ /- 0 : nat.
Γ /- succ(M1) : nat                   :- Γ /- M1 : nat.
Γ /- pred(M1) : nat                   :- Γ /- M1 : nat.
Γ /- iszero(M1) : bool                :- Γ /- M1 : nat.
Γ /- X : T                            :- x(X), member(X:T, Γ).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- [X:T1|Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : (T11 -> T12), Γ /- M2 : T11. 
% ------------------------   MAIN  ------------------------

show(X : T) :- format('~w : ~w\n', [X, T]).

run(X : T, Γ, [X:T|Γ]) :- x(X), t(T), show(X : T).
run(M, Γ, Γ)           :- m(M), !, Γ /- M ==>> M_, !, Γ /- M_ : T, !, writeln(M_ : T).

run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]). 
% lambda x:Bool. x;
:- run([(fn(x : bool) -> x)]). 
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true); 
:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $
           (fn(x : bool) -> if(x, false, true))]).  
% lambda x:Nat. succ x;
:- run([(fn(x : nat) -> succ(x))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]).

:- halt.
