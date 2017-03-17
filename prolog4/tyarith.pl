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
 % ------------------------   SYNTAX  ------------------------
:- use_module(rtg).
t ::=             % 型:
bool       % ブール値型
| nat        % 自然数型
.
m ::=             % 項:
true       % 真
| false      % 偽
| if(m, m, m)  % 条件式
| 0       % ゼロ
| succ(m)    % 後者値
| pred(m)    % 前者値
| iszero(m)  % ゼロ判定
.
n ::=             % 数値:
0       % ゼロ
| succ(n)    % 後者値
.
v ::=             % 値:
true       % 真
| false      % 偽
| n          % 数値
. 

% ------------------------   EVALUATION  ------------------------

if(true, M2, _) ==> M2.
if(false, _, M3) ==> M3.
if(M1, M2, M3) ==> if(M1_, M2, M3) where M1 ==> M1_.
succ(M1) ==> succ(M1_) where M1 ==> M1_.
pred(0) ==> 0.
pred(succ(N1)) ==> N1 where n(N1).
pred(M1) ==> pred(M1_) where M1 ==> M1_.
iszero(0) ==> true.
iszero(succ(N1)) ==> false where n(N1).
iszero(M1) ==> iszero(M1_) where M1 ==> M1_.
M ==>> M_ where M ==> M1, M1 ==>> M_.
M ==>> M. 

% ------------------------   TYPING  ------------------------

/- true : bool.
/- false : bool.
/- if(M1, M2, M3) : T2 where /- M1 : bool, /- M2 : T2, /- M3 : T2.
/- 0 : nat.
/- succ(M1) : nat where /- M1 : nat.
/- pred(M1) : nat where /- M1 : nat.
/- iszero(M1) : bool where /- M1 : nat. 

% ------------------------   MAIN  ------------------------

run(M, Γ, Γ) :- !, m(M), !, /- M : T, !, M ==>> M_, !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% true;

:- run([true]). 
% if false then true else false;

:- run([if(false, true, false)]). 
% 0;

:- run([0]). 
% succ (pred 0);

:- run([succ(pred(0))]). 
% iszero (pred (succ (succ 0)));

:- run([iszero(pred(succ(succ(0))))]). 
% iszero (pred (pred (succ (succ 0))));

:- run([iszero(pred(pred(succ(succ(0)))))]). 
% iszero 0;

:- run([iszero(0)]).
:- halt.

