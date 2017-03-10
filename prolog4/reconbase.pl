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
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= bool | nat | true | false | 0.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).  % 識別子:

t ::=                                % 型:
bool                          % ブール値型
| nat                           % 自然数型
| x                             % 型変数
| (t -> t)                      % 関数の型
.
m ::=                                % 項:
true                          % 真
| false                         % 偽
| if(m, m, m)                     % 条件式
| 0                          % ゼロ
| succ(m)                       % 後者値
| pred(m)                       % 前者値
| iszero(m)                     % ゼロ判定
| x                             % 変数
| (fn(x : t) -> m)                     % ラムダ抽象
| m $ m                      % 関数適用
.
n ::=                                % 数値:
0                          % ゼロ
| succ(n)                       % 後者値
.
v ::=                                % 値:
true                          % 真
| false                         % 偽
| n                             % 数値
| (fn(x : t) -> m)                     % ラムダ抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_. 
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.

T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_ :- T![(J -> M)] subst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(Γ,M)),fail.

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
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_. 
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : bool, Γ /- M2 : T2, Γ /- M3 : T2.
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : nat.
Γ /- pred(M1) : nat where Γ /- M1 : nat.
Γ /- iszero(M1) : bool where Γ /- M1 : nat.
Γ /- X : T where x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T11. 
%typeof(Γ,M,_) :- writeln(error:typeof(M)),halt.

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(M, Γ, Γ) :- !, m(M), !, Γ /- M ==>> M_, !, Γ /- M_ : T, !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda x:A. x;

:- run([(fn(x : 'A') -> x)]). 
% lambda x:Bool. x;

:- run([(fn(x : bool) -> x)]). 
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true); 

:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true))]).  
% lambda x:Nat. succ x;

:- run([(fn(x : nat) -> succ(x))]).  
% (lambda x:Nat. succ (succ x)) (succ 0); 

:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]).
:- halt.

