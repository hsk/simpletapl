:- discontiguous((/-)/2).
:- op(1100, xfy, [in]).
:- op(1050, xfy, [=>]).
:- op(920, xfx, [==>, ==>>]).
:- op(910, xfx, [/-]).
:- op(600, xfy, [::, as]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | true | false. % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), sub_atom(X, 0, 1, _, P), (char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:

t ::=                       % 型:
      bool                  % ブール値型
    | nat                   % 自然数型
    | tx                    % 型変数
    | (t -> t)              % 関数の型
    | (all(tx) => t)        % 全称型
    .
m ::=                       % 項:
      true                  % 真
    | false                 % 偽
    | if(m, m, m)           % 条件式
    | 0                     % ゼロ
    | succ(m)               % 後者値
    | pred(m)               % 前者値
    | iszero(m)             % ゼロ判定
    | x                     % 変数
    | (fn(x : t) -> m)      % ラムダ抽象
    | m $ m                 % 関数適用
    | (let(x) = m in m)     % let束縛
    | m as t                % 型指定
    | (fn(tx) => m) | m![t] % 型適用
    .
n ::=                       % 数値:
      0                     % ゼロ
    | succ(n)               % 後者値
    .
v ::=                       % 値:
      true                  % 真
    | false                 % 偽
    | n                     % 数値
    | (fn(x : t) -> m)      % ラムダ抽象
    | (fn(tx) => m)
    .

% ------------------------   SUBSTITUTION  ------------------------

bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
J![(J -> S)] tsubst S                              :- tx(J).
X![(J -> S)] tsubst X                              :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_)          :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX) => T2)![(J -> S)] tsubst (all(TX) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                         :- T![(J -> S)] tsubst T_. 

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_,
                                                     M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_)               :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_)               :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_)           :- M1![(J -> M)] subst M1_.
J![(J -> M)] subst M                              :- x(J).
X![(J -> M)] subst X                              :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_)
                                                  :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)              :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_)
                                                  :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
(M1 as T1)![(J -> M)] subst (M1_ as T1)           :- M1![(J -> M)] subst M1_.
(fn(TX) => M2)![(J -> M)] subst (fn(TX) => M2_)   :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2])               :- M1![(J -> M)] subst M1_.
M1![(J -> M)] subst M1.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_                         :- T![(J -> M)] subst T_.

true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_,
                                                       M3![(J -> S)] tmsubst M3_.
0![(J -> S)] tmsubst 0.
succ(M1)![(J -> S)] tmsubst succ(M1_)               :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_)               :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_)           :- M1![(J -> S)] tmsubst M1_.
X![(J -> S)] tmsubst X                              :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_)
                                                    :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_)              :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(let(X) = M1 in M2)![(J -> S)] tmsubst (let(X) = M1_ in M2_)
                                                    :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(M1 as T1)![(J -> S)] tmsubst (M1_ as T1_)          :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
(fn(TX) => M2)![(J -> S)] tmsubst (fn(TX) => M2_)   :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_])              :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_                         :- T![(J -> S)] tmsubst T_.

gett(Γ, X, T) :- member(X:T, Γ).
gett(Γ, X, T) :- member(X:T=_, Γ). 

% ------------------------   EVALUATION  ------------------------

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3)           :- Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_)                       :- Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1                        :- n(N1).
Γ /- pred(M1) ==> pred(M1_)                       :- Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false                   :- n(N1).
Γ /- iszero(M1) ==> iszero(M1_)                   :- Γ /- M1 ==> M1_.
Γ /- X ==> M                                      :- x(X), member(X:_=M,Γ).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R              :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_                         :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2                         :- Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_                  :- v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) :- Γ /- M1 ==> M1_.
Γ /- V1 as T ==> V1                               :- v(V1).
Γ /- M1 as T ==> M1_ as T                         :- Γ /- M1 ==> M1_.
Γ /- (fn(X) => M11)![T2] ==> M11_                 :- M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2]                         :- Γ /- M1 ==> M1_. 

Γ /- M ==>> M_ :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.

gettabb(Γ, X, T)   :- member(X :: T, Γ).
compute(Γ, X, T)   :- tx(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).

Γ /- S = T                              :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- X == T                             :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X                             :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X                             :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2)           :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- (all(TX1) => S2) == (all(_) => T2) :- [TX1 - name | Γ] /- S2 = T2. 

% ------------------------   TYPING  ------------------------

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2              :- Γ /- M1 : T1, Γ /- T1 = bool,
                                            Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- 0 : nat.
Γ /- succ(M1) : nat                   :- Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- pred(M1) : nat                   :- Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- iszero(M1) : bool                :- Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- X : T                            :- x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- [X:T1|Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)),
                                            Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T          :- Γ /- M1 : T1, [X:T1|Γ] /- M2 : T.
Γ /- (M1 as T) : T                    :- Γ /- M1 : T1, Γ /- T1 = T.
Γ /- (fn(TX) => M2) : (all(TX) => T2) :- [TX - tvar | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_                   :- Γ /- M1 : T1, simplify(Γ, T1, (all(X) => T12)),
                                            T12![(X -> T2)] tsubst T12_.
Γ /- M : _                            :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X : T)  :- !,format('~w : ~w\n', [X, T]).
show(X :: T) :- !,format('~w :: *\n', [X]).
show(X)      :- writeln(X).

run(type(X), Γ, [X-tvar|Γ])   :- tx(X), show(X).
run(type(X) = T, Γ, [X::T|Γ]) :- tx(X), t(T), show(X :: T).
run(X : T, Γ, [X:T|Γ])        :- x(X), t(T), show(X : T).
run(X : T = M, Γ, [X:T=M_|Γ]) :- x(X), t(T), m(M), Γ /- M : T_, Γ /- T_ = T,
                                 Γ /- M ==>> M_, show(X : T).
run(X = M, Γ, [X:T=M_|Γ])     :- x(X), m(M), Γ /- M : T, Γ /- M ==>> M_, show(X : T).
run(M, Γ, Γ)                  :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).

run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

:- run([
  (fn(x : bool) -> x),
  (fn(x : bool) -> fn(x : bool) -> x),
  (fn(x : (bool -> bool)) -> if(x $ false, true, false)) $
    (fn(x : bool) -> if(x, false, true)),
  a : bool,
  a,
  (fn(x : bool) -> x) $ a,
  (fn(x : bool) -> (fn(x : bool) -> x) $ x) $ a,
  (fn(x : bool) -> x) $ true,
  (fn(x : bool) -> (fn(x : bool) -> x) $ x) $ true
]). 

% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]).
:- run([(let(x) = true in x)]). 
% lambda x:Bool. x;
:- run([(fn(x : bool) -> x)]).
:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $
           (fn(x : bool) -> if(x, false, true))]).
:- run([(fn(x : nat) -> succ(x))]).
:- run([(fn(x : nat) -> x) $ 0]).
:- run([(fn(x : nat) -> x) $ succ(0)]).
:- run([(fn(x : nat) -> succ(x)) $ 0]).
:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]).
:- run([type('T') = (nat -> nat)]).
:- run([type('T') = (nat -> nat),
        (fn(f : (nat -> nat)) -> fn(x : nat) -> f $ (f $ x))]).
:- run([type('T') = (nat -> nat),
        (fn(f : 'T') -> f)]).
:- run([type('T') = (nat -> nat),
        (fn(f : 'T') -> f $ 0)]).
:- run([type('T') = (nat -> nat),
        (fn(f : 'T') -> fn(x : nat) -> f $ (f $ x))]).
:- run([(fn('X') => fn(x : 'X') -> x)]).
:- run([(fn('X') => fn(x : 'X') -> x)![(all('X') => 'X' -> 'X')]]).

:- halt.
