:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1100, xfy, [in]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(910, fx, ['/-']).
:- op(600, xfy, ['::', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2, '<-']).
:- op(400, yfx, ['#']).
term_expansion((A where B), (A :- B)).
:- op(600, xfy, ['::']).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
syntax(x).
x(X) :- atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_').  % 識別子:

syntax(tx).
tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper).  % 型変数:

k ::=              % カインド:
'*'           % 真の型のカインド
| (k => k)   % 演算子のカインド
.
t ::=              % 型:
tx           % 型変数
| (t -> t)    % 関数の型
| (all(tx :: k) => t)  % 全称型
| (fn(tx :: k) => t)  % 型抽象
| t $ t    % 関数適用
.
m ::=              % 項:
x           % 変数
| (fn(x : t) -> m)   % ラムダ抽象
| m $ m    % 関数適用
| (fn(tx <: k) => m)  % 型抽象
| m![t]   % 型適用
.
v ::=              % 値:
(fn(x : t) -> m)   % ラムダ抽象 
| (fn(tx <: k) => m)  % 型抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

J![(J -> S)] tsubst S :- tx(J).
X![(J -> S)] tsubst X :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX :: K) => T2)![(J -> S)] tsubst (all(TX :: K) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
(fn(TX :: K) => T2)![(J -> S)] tsubst (fn(TX :: K) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![(J -> S)] tsubst T_ :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_. 

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

J![(J -> M)] subst M :- x(J).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(fn(TX <: K) => M2)![(J -> M)] subst (fn(TX <: K) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
M1![(J -> M)] subst M1.
A![(J -> M)] subst B :- writeln(error : A![(J -> M)] subst B), fail.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_ :- T![(J -> M)] subst T_.
X![(J -> S)] tmsubst X :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(fn(TX <: K) => M2)![(J -> S)] tmsubst (fn(TX <: K) => M2_) :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(M)),fail.

Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (fn(X <: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_. 
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   KINDING  ------------------------

compute(Γ, (fn(X :: _) => T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- X == X :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- (all(TX1 :: K1) => S2) == (all(_ :: K2) => T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- (fn(TX1 :: K1) => S2) == (fn(_ :: K2) => T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !.
Γ /- T :: K where writeln(error : kindof(T, K)), fail.
Γ \- X :: '*' where tx(X), \+ member(X - _, Γ).
Γ \- X :: K where tx(X), !, getb(Γ, X, bTVar(K)).
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- (all(TX :: K1) => T2) :: '*' where !, [TX - bTVar(K1) | Γ] /- T2 :: '*'.
Γ \- (fn(TX :: K1) => T2) :: (K1 => K) where !, [TX - bTVar(K1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- T :: '*'. 

% ------------------------   TYPING  ------------------------ *)

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (fn(TX <: K1) => M2) : (all(TX :: K1) => T2) where [TX - bTVar(K1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- T2 :: K2, Γ /- M1 : T1, simplify(Γ, T1, (all(X :: K2) => T12)), T12![(X -> T2)] tsubst T12_.
Γ /- M : _ where writeln(error : typeof(M)), !, halt.
show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar(K1)) :- format('~w :: ~w\n', [X, K1]).
run(X : T, Γ, [X - bVar(T) | Γ]) :- x(X), t(T), show(Γ, X, bVar(T)).
run(X :: K, Γ, [X - bTVar(K) | Γ]) :- tx(X), k(K), show(Γ, X, bTVar(K)).
run(M, Γ, Γ) :- !, m(M), !, Γ /- M : T, Γ /- M ==>> M_, !, writeln(M_ : T), !.
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

