:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(920, xfx, [==>, ==>>]).
:- op(910, xfx, [/-, \-]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2]).
:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
x ::= atom.           % 識別子
t ::=                 % 型:
      (t -> t)        % 関数の型
    | rec(x, t)       % 再帰型
    | x               % 型変数
    .
m ::=                 % 項:
      x               % 変数
    | (fn(x : t)-> m) % ラムダ抽象
    | m $ m           % 関数適用
    .
v ::=                 % 値:
      fn(x : t) -> m  % ラムダ抽象
    .

% ------------------------   SUBSTITUTION  ------------------------

                  J![(J -> S)] tsubst S                   :- x(J).
                  X![(J -> S)] tsubst X                   :- x(X).
         (T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_)        :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
         rec(X, T1)![(J -> S)] tsubst rec(X, T1_)         :- T1![X, (J -> S)] tsubst2 T1_.
               T![X, (X -> S)] tsubst2 T.
               T![X, (J -> S)] tsubst2 T_                 :- T![(J -> S)] tsubst T_.

                  J![(J -> M)] subst M                    :- x(J).
                  X![(J -> M)] subst X                    :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
            M1 $ M2![(J -> M)] subst (M1_ $ M2_)          :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
               S![J, (J -> M)] subst2 S.
               S![X, (J -> M)] subst2 M_                  :- S![(J -> M)] subst M_.

% ------------------------   EVALUATION  ------------------------

Γ /- (fn(X) -> M12) $ V2 ==> R        :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2             ==> V1 $ M2_ :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2             ==> M1_ $ M2 :- Γ /- M1 ==> M1_.
Γ /- M                  ==>> M_       :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M                  ==>> M.

compute(Γ, rec(X, S1), T) :- S1![(X -> rec(X, S1))] tsubst T.
simplify(Γ, T, T_)        :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).

Γ          /-          S = T          :- ([] ; Γ) \- S = T.
(Seen ; Γ) \-          S = T          :- member((S, T), Seen).
(Seen ; Γ) \-          X = Y          :- x(X), x(Y).
(Seen ; Γ) \- (S1 -> S2) = (T1 -> T2) :- (Seen ; Γ) \- S1 = T1, (Seen ; Γ) \- S2 = T2.
(Seen ; Γ) \- rec(X, S1) = T          :- S = rec(X, S1), S1![(X -> S)] tsubst S1_, ([(S, T) | Seen] ; Γ) \- S1_ = T.
(Seen ; Γ) \-          S = rec(X, T1) :- T = rec(X, T1), T1![(X -> T)] tsubst T1_, ([(S, T) | Seen] ; Γ) \- S = T1_.

Γ /-                  X : T           :- x(X), member(X : T, Γ).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- [X : T1 | Γ] /- M2 : T2_.
Γ /-            M1 $ M2 : T12         :- Γ /- M1 : T1, Γ /- M2 : T2, simplify(Γ, T1, (T11 -> T12)), Γ /- T2 = T11.

% ------------------------   MAIN  ------------------------

show(X : T)    :- format('~w : ~w\n', [X, T]).
show(X - type) :- format('~w\n', [X]).
run(X : T, Γ, [X : T | Γ]) :- show(X : T).
run(type(X), Γ, [T - type | Γ]) :- show(X - type).
run(M, Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, [], _).

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]).
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([(fn(f : rec('X', ('A' -> 'A'))) -> (fn(x : 'A') -> f $ x))]).
% lambda x:T. x;
:- run([(fn(x : 'T') -> x)]).
% T;
% i : T;
% i;
:- run([type('T'), i : 'T', i]).

:- halt.

