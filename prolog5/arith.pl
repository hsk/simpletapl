:- op(920, xfx, ['→', '↠']).
:- use_module(rtg).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

m ::=             % 項:
      true        % 真
    | false       % 偽
    | if(m, m, m) % 条件式
    | 0           % ゼロ
    | succ(m)     % 後者値
    | pred(m)     % 前者値
    | iszero(m)   % ゼロ判定
    .
n ::=             % 数値:
      0           % ゼロ
    | succ(n)     % 後者値
    .
v ::=             % 値:
      true        % 真
    | false       % 偽
    | n           % 数値
    .

% ------------------------   EVALUATION  ------------------------

if(true, M2, _) → M2.
if(false, _, M3) → M3.
if(M1, M2, M3) → if(M1_, M2, M3) :- M1 → M1_.
succ(M1) → succ(M1_)             :- M1 → M1_.
pred(0) → 0.
pred(succ(N1)) → N1              :- n(N1).
pred(M1) → pred(M1_)             :- M1 → M1_.
iszero(0) → true.
iszero(succ(N1)) → false         :- n(N1).
iszero(M1) → iszero(M1_)         :- M1 → M1_.
M ↠ M_                           :- M → M1, M1 ↠ M_.
M ↠ M.

% ------------------------   MAIN  ------------------------

run(M, Γ, Γ) :- !, m(M), !, M ↠ M_, !, writeln(M_).
run(Ls)      :- foldl(run, Ls, [], _).

% ------------------------   TEST  ------------------------

:- run([true]).
:- run([if(false, true, false)]).
:- run([0]).
:- run([succ(pred(0))]).
:- run([iszero(pred(succ(succ(0))))]).
:- run([iszero(pred(pred(succ(succ(0)))))]).
:- run([iszero(0)]).
:- run([if(0, succ(pred(0)), 0)]).
:- run([if(0, succ(succ(0)), 0)]).
:- run([if(0, succ(pred(succ(0))), 0)]).

:- halt.
