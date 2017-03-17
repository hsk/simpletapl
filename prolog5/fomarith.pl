:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1100, xfy, [in]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2, '<-']).
:- op(400, yfx, ['#']).
term_expansion((A where B), (A :- B)).
:- op(600, xfy, ['::']).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | true | false | 0.  % キーワード:

syntax(x). x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_').  % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper).  % 型変数:

k ::=                     % カインド:
      '*'                 % 真の型のカインド
    | (k => k)            % 演算子のカインド
    .
t ::=                     % 型:
      bool                % ブール値型
    | nat                 % 自然数型
    | tx                  % 型変数
    | (t -> t)            % 関数の型
    | (all(tx :: k) => t) % 全称型
    | (fn(tx :: k) => t)  % 型抽象
    | t $ t               % 関数適用
    .
m ::=                     % 項:
      true                % 真
    | false               % 偽
    | if(m, m, m)         % 条件式
    | 0                   % ゼロ
    | succ(m)             % 後者値
    | pred(m)             % 前者値
    | iszero(m)           % ゼロ判定
    | x                   % 変数
    | (fn(x : t) -> m)    % ラムダ抽象
    | m $ m               % 関数適用
    | (let(x) = m in m)   % let束縛
    | m as t              % 型指定
    | (fn(tx <: k) => m)  % 型抽象
    | m![t]               % 型適用
    .
n ::=                     % 数値:
      0                   % ゼロ
    | succ(n)             % 後者値
    .
v ::=                     % 値:
      true                % 真
    | false               % 偽
    | n                   % 数値
    | (fn(x : t) -> m)    % ラムダ抽象
    | (fn(tx <: k) => m)  % 型抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
J![(J -> S)] tsubst S                                      :- tx(J).
X![(J -> S)] tsubst X                                      :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_)                  :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX :: K) => T2)![(J -> S)] tsubst (all(TX :: K) => T2_)
                                                           :- T2![TX, (J -> S)] tsubst2 T2_.
(fn(TX :: K) => T2)![(J -> S)] tsubst (fn(TX :: K) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_)                      :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![(J -> S)] tsubst T_                                     :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                                 :- T![(J -> S)] tsubst T_. 

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_)            :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_,
                                                                M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_)                          :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_)                          :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_)                      :- M1![(J -> M)] subst M1_.
J![(J -> M)] subst M                                         :- x(J).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_)    :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                         :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_)   :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
(M1 as T1)![(J -> M)] subst (M1_ as T1)                      :- M1![(J -> M)] subst M1_.
(fn(TX <: K) => M2)![(J -> M)] subst (fn(TX <: K) => M2_)    :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2])                          :- M1![(J -> M)] subst M1_.
M1![(J -> M)] subst M1.
A![(J -> M)] subst B                                         :- writeln(error : A![(J -> M)] subst B), fail.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_                                    :- T![(J -> M)] subst T_.

true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_)          :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_,
                                                                M3![(J -> S)] tmsubst M3_.
0![(J -> S)] tmsubst 0.
succ(M1)![(J -> S)] tmsubst succ(M1_)                        :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_)                        :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_)                    :- M1![(J -> S)] tmsubst M1_.
X![(J -> S)] tmsubst X                                       :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_)   :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_)                       :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(let(X) = M1 in M2)![(J -> S)] tmsubst (let(X) = M1_ in M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(M1 as T1)![(J -> S)] tmsubst (M1_ as T1_)                   :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
(fn(TX <: K) => M2)![(J -> S)] tmsubst (fn(TX <: K) => M2_)  :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_])                       :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_                                  :- T![(J -> S)] tmsubst T_.

getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(M)),fail.

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_) where Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1 where n(N1).
Γ /- pred(M1) ==> pred(M1_) where Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false where n(N1).
Γ /- iszero(M1) ==> iszero(M1_) where Γ /- M1 ==> M1_.
Γ /- X ==> M where x(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) where Γ /- M1 ==> M1_.
Γ /- V1 as T ==> V1 where v(V1).
Γ /- M1 as T ==> M1_ as T where Γ /- M1 ==> M1_.
Γ /- (fn(X <: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_. 
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T) :- tx(X), gettabb(Γ, X, T).
compute(Γ, (fn(X :: _) => T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- X == T :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- (all(TX1 :: K1) => S2) == (all(_ :: K2) => T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- (fn(TX1 :: K1) => S2) == (fn(_ :: K2) => T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !. 
%kindof(Γ,T,K) :- writeln(error:kindof(T,K)),fail.

Γ \- X :: '*' where tx(X), \+ member(X - _, Γ).
Γ \- X :: K where tx(X), getb(Γ, X, bTVar(K)), !.
Γ \- X :: K where tx(X), !, getb(Γ, X, bTAbb(_, K)).
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- (all(TX :: K1) => T2) :: '*' where !, [TX - bTVar(K1) | Γ] /- T2 :: '*'.
Γ \- (fn(TX :: K1) => T2) :: (K1 => K) where !, [TX - bTVar(K1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- T :: '*'. 

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- (M1 as T) : T where Γ /- T :: '*', Γ /- M1 : T1, Γ /- T1 = T.
Γ /- (fn(TX <: K1) => M2) : (all(TX :: K1) => T2) where [TX - bTVar(K1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- T2 :: K2, Γ /- M1 : T1, simplify(Γ, T1, (all(X :: K2) => T12)), T12![(X -> T2)] tsubst T12_. 

%typeof(Γ,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar(K1)) :- format('~w :: ~w\n', [X, K1]).
show(Γ, X, bMAbb(M, T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTAbb(T, K)) :- format('~w :: ~w\n', [X, K]).
run(type(X) = T, Γ, [X - Bind | Γ]) :- tx(X), t(T), Γ /- T :: K, bTAbb(T, K) = Bind, show(Γ, X, Bind), !.
run(type(X :: K) = T, Γ, [X - bTAbb(T, K) | Γ]) :- tx(X), k(K), t(T), Γ /- T :: K, show(Γ, X, bTAbb(T, K)), !.
run(X :: K, Γ, [X - bTVar(K) | Γ]) :- tx(X), k(K), show(Γ, X, bTVar(K)), !.
run(X : T, Γ, [X - bVar(T) | Γ]) :- x(X), t(T), show(Γ, X, bVar(T)).
run(X : T = M, Γ, [X - bMAbb(M_, T) | Γ]) :- x(X), t(T), m(M), Γ /- M ==>> M_, show(Γ, X, bMAbb(M_, T), S), !.
run(X = M, Γ, [X - bMAbb(M_, T) | Γ]) :- x(X), m(M), Γ /- M : T, Γ /- M ==>> M_, show(Γ, X, bMAbb(M_, T)), !.
run(M, Γ, Γ) :- !, m(M), !, Γ /- M : T, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(Ls) :- foldl(run, Ls, [], Γ). 

% ------------------------   TEST  ------------------------

:- run([(fn(x : bool) -> x), (fn(x : bool) -> fn(x : bool) -> x), (fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)), a : bool, a, (fn(x : bool) -> x) $ a, (fn(x : bool) -> (fn(x : bool) -> x) $ x) $ a, (fn(x : bool) -> x) $ true, (fn(x : bool) -> (fn(x : bool) -> x) $ x) $ true]). 

% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]).
:- run([(let(x) = true in x)]).
:- run([(fn(x : bool) -> x)]).
:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true))]).
:- run([(fn(x : nat) -> succ(x))]).
:- run([(fn(x : nat) -> x) $ 0]).
:- run([(fn(x : nat) -> x) $ succ(0)]).
:- run([(fn(x : nat) -> succ(x)) $ 0]).
:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]).
:- run([type('T') = (nat -> nat)]).
:- run([type('T') = (nat -> nat), (fn(f : 'T') -> fn(x : nat) -> f $ (f $ x))]).
:- run([type('T') = (nat -> nat), (fn(f : 'T') -> f)]).
:- run([type('T') = (nat -> nat), (fn(f : 'T') -> f $ 0)]).
:- run([type('T') = (nat -> nat), (fn(f : 'T') -> fn(x : nat) -> f $ (f $ x))]). 

% lambda X. lambda x:X. x;
:- run([(fn('X' <: '*') => fn(x : 'X') -> x)]). 
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([(fn('X' <: '*') => fn(x : 'X') -> x)![(all('X' :: '*') => 'X' -> 'X')]]).
:- run([ 
% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;
type('Pair') = (fn('X' :: '*') => fn('Y' :: '*') => all('R' :: '*') => ('X' -> 'Y' -> 'R') -> 'R'),  
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;
pair = (fn('X' <: '*') => fn('Y' <: '*') => fn(x : 'X') -> fn(y : 'Y') -> fn('R' <: '*') => fn(p : ('X' -> 'Y' -> 'R')) -> p $ x $ y),  
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
fst = (fn('X' <: '*') => fn('Y' <: '*') => fn(p : 'Pair' $ 'X' $ 'Y') -> p!['X'] $ (fn(x : 'X') -> fn(y : 'Y') -> x)),  
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);
snd = (fn('X' <: '*') => fn('Y' <: '*') => fn(p : 'Pair' $ 'X' $ 'Y') -> p!['Y'] $ (fn(x : 'X') -> fn(y : 'Y') -> y)),  
% pr = pair [Nat] [Bool] 0 false;
pr = pair![nat]![bool] $ 0 $ false, fst![nat]![bool] $ pr, snd![nat]![bool] $ pr
]).

:- halt.

