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
 % ------------------------   SYNTAX  ------------------------
:- use_module(rtg).
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

% ------------------------   MAIN  ------------------------

run(eval(M), Γ, Γ) :- !, m(M), !, M ==>> M_, !, writeln(M_).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

:- run([eval(true)]).
:- run([eval(if(false, true, false))]).
:- run([eval(0)]).
:- run([eval(succ(pred(0)))]).
:- run([eval(iszero(pred(succ(succ(0)))))]).
:- run([eval(iszero(pred(pred(succ(succ(0))))))]).
:- run([eval(iszero(0))]).
:- run([eval(if(0, succ(pred(0)), 0))]).
:- run([eval(if(0, succ(succ(0)), 0))]).
:- run([eval(if(0, succ(pred(succ(0))), 0))]).
:- halt.

