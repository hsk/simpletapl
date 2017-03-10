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
:- op(600, xfy, ['<:']).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= top.                          % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).  % 識別子:

t ::=                                % 型
top                           % 最大の型
| x                             % 変数
| (t -> t)                      % 関数の型
| (all(x :: t) => t)                    % 全称型
.
m ::=                                % 項
x                             % 変数
| (fn(x : t) -> m)                     % ラムダ抽象
| m $ m                      % 関数適用
| (fn(x :: t) => m)                    % 型抽象
| m![t]                     % 型適用
.
v ::=                                % 値:
(fn(x : t) -> m)                     % ラムダ抽象
| (fn(x :: t) => m)                    % 型抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(fn(TX :: T1) => M2)![(J -> M)] subst (fn(TX :: T1) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
A![(J -> M)] subst B :- writeln(error : A![(J -> M)] subst B), fail.
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_ :- T![(J -> M)] subst T_.
X![(J -> S)] tmsubst X :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(fn(TX :: T1) => M2)![(J -> S)] tmsubst (fn(TX :: T1_) => M2_) :- T1![(J -> S)] tsubst T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)), !.
gett(Γ, X, _) :- writeln(error : gett(Γ, X)), fail. 

% ------------------------   EVALUATION  ------------------------

Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_. 
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

promote(Γ, X, T) :- x(X), getb(Γ, X, bTVar(T)).
Γ /- T1 <: T2 where T1 = T2.
Γ /- _ <: top.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ /- X <: T where x(X), promote(Γ, X, S), Γ /- S <: T.
Γ /- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2. 

% ------------------------   TYPING  ------------------------

lcst(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst(Γ, T, T). 

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (fn(TX :: T1) => M2) : (all(TX :: T1) => T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)), Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar(T)) :- format('~w <: ~w\n', [X, T]).
run(X : T, Γ, [X - bVar(T) | Γ]) :- show(Γ, X, bVar(T)).
run(X <: T, Γ, [X - bTVar(T) | Γ]) :- show(Γ, X, bTVar(T)).
run(M, Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;

:- run([(fn('X' :: top) => (fn(x : 'X') -> x))]). 
% (lambda X. lambda x:X. x) [All X.X->X];

:- run([(fn('X' :: top) => (fn(x : 'X') -> x))![(all('X' :: top) => ('X' -> 'X'))]]). 
%lambda x:Top. x;

:- run([(fn(x : top) -> x)]). 
%(lambda x:Top. x) (lambda x:Top. x);

:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
%(lambda x:Top->Top. x) (lambda x:Top. x);

:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
%lambda X<:Top->Top. lambda x:X. x x;

:- run([(fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x))]). 
%x : Top;
%x;

:- run([x : top, x]). 
%T <: Top->Top;
%x : T;

:- run(['T' <: (top -> top), x : 'T']).
:- halt.

