:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1050, xfy, [=>]).
:- op(920, xfx, [==>, ==>>, <:]).
:- op(910, xfx, [/-, \-]).
:- op(600, xfy, [::]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

syntax(x). x(X) :- atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_').  % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper).  % 型変数:

k ::=                     % カインド:
      '*'                 % 真の型のカインド
    | (k => k)            % 演算子のカインド
    .
t ::=                     % 型:
      tx                  % 型変数
    | (t -> t)            % 関数の型
    | (all(tx :: k) => t) % 全称型
    | (fn(tx :: k) => t)  % 型抽象
    | t $ t               % 関数適用
    .
m ::=                     % 項:
      x                   % 変数
    | (fn(x : t) -> m)    % ラムダ抽象
    | m $ m               % 関数適用
    | (fn(tx <: k) => m)  % 型抽象
    | m![t]               % 型適用
    .
v ::=                     % 値:
      (fn(x : t) -> m)    % ラムダ抽象 
    | (fn(tx <: k) => m)  % 型抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

J![(J -> S)] tsubst S                     :- tx(J).
X![(J -> S)] tsubst X                     :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX :: K) => T2)![(J -> S)] tsubst (all(TX :: K) => T2_)
                                          :- T2![TX, (J -> S)] tsubst2 T2_.
(fn(TX :: K) => T2)![(J -> S)] tsubst (fn(TX :: K) => T2_)
                                          :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_)     :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![(J -> S)] tsubst T_                    :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                :- T![(J -> S)] tsubst T_. 

J![(J -> M)] subst M                 :- x(J).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_)
                                     :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(fn(TX <: K) => M2)![(J -> M)] subst (fn(TX <: K) => M2_)
                                     :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2])  :- M1![(J -> M)] subst M1_.
M1![(J -> M)] subst M1.
A![(J -> M)] subst B                 :- writeln(error : A![(J -> M)] subst B), fail.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_            :- T![(J -> M)] subst T_.

X![(J -> S)] tmsubst X                 :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_)
                                       :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(fn(TX <: K) => M2)![(J -> S)] tmsubst (fn(TX <: K) => M2_)
                                       :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_            :- T![(J -> S)] tmsubst T_.

% ------------------------   EVALUATION  ------------------------

Γ /- (fn(X : T11) -> M12) $ V2 ==> R   :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_              :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2              :- Γ /- M1 ==> M1_.
Γ /- (fn(X <: _) => M11)![T2] ==> M11_ :- M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2]              :- Γ /- M1 ==> M1_. 

Γ /- M ==>> M_ :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   KINDING  ------------------------

compute(Γ, (fn(X :: _) => T12) $ T2, T) :- T12![(X -> T2)] tsubst T.

simplify(Γ, T1 $ T2, T_)                :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_)                      :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_)                     :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).

Γ /- S = T                                          :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- X == X                                         :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2)                       :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- (all(TX1 :: K1) => S2) == (all(_ :: K2) => T2) :- K1 = K2, [TX1-name|Γ] /- S2 = T2.
Γ /- (fn(TX1 :: K1) => S2) == (fn(_ :: K2) => T2)   :- K1 = K2, [TX1-name|Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2                             :- Γ /- S1 = T1, Γ /- S2 = T2.

Γ /- T :: K                            :- Γ \- T :: K, !.
Γ /- T :: K                            :- writeln(error : kindof(T, K)), fail.
Γ \- X :: '*'                          :- tx(X), \+ member(X - _, Γ).
Γ \- X :: K                            :- tx(X), !, member(X :: K, Γ).
Γ \- (T1 -> T2) :: '*'                 :- !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- (all(TX :: K1) => T2) :: '*'      :- !, [TX :: K1 | Γ] /- T2 :: '*'.
Γ \- (fn(TX :: K1) => T2) :: (K1 => K) :- !, [TX :: K1 | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12                    :- !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- T :: '*'. 

% ------------------------   TYPING  ------------------------ *)

Γ /- X : T                            :- x(X), !, member(X : T, Γ).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- Γ /- T1 :: '*', [X : T1 | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)),
                                         Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (fn(TX <: K1) => M2) : (all(TX :: K1) => T2)
                                      :- [TX :: K1 | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_                   :- Γ /- T2 :: K2, Γ /- M1 : T1,
                                         simplify(Γ, T1, (all(X :: K2) => T12)),
                                         T12![(X -> T2)] tsubst T12_.
Γ /- M : _                            :- writeln(error : typeof(M)), !, halt.

show(X : T)  :- format('~w : ~w\n', [X, T]).
show(X :: K) :- format('~w :: ~w\n', [X, K]).

run(X : T, Γ, [X:T|Γ])   :- x(X), t(T), show(X : T).
run(X :: K, Γ, [X::K|Γ]) :- tx(X), k(K), show(X :: K).
run(M, Γ, Γ)             :- !, m(M), !, Γ /- M : T, Γ /- M ==>> M_, !, writeln(M_ : T), !.

run(Ls) :- foldl(run, Ls, [], Γ). 

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([(fn('X' <: '*') => fn(x : 'X') -> x)]). 
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([(fn('X' <: '*') => fn(x : 'X') -> x)![(all('X' :: '*') => 'X' -> 'X')]]). 
% T :: *;
% k : T;
:- run(['T' :: '*', k : 'T']). 
% TT :: * => *;
% kk : TT;
:- run(['TT' :: ('*' => '*'), kk : 'TT']). 
% T :: *;
% x : (lambda X::*=>*.T) T;
:- run(['T' :: '*', x : (fn('X' :: ('*' => '*')) => 'T') $ 'T']).

:- halt.

