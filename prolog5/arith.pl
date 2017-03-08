:- op(1200, xfx, ['--', where]).
:- op(920, xfx, ['==>', '==>>']).

term_expansion((A where B), (A :- B)).

% 構文

m(M) :-                                           % 項:
        M = true                                  % 定数真
      ; M = false                                 % 定数偽
      ; M = if(M1, M2, M3), m(M1), m(M2), m(M3)   % 条件式
      ; M = 0                                     % 定数ゼロ
      ; M = succ(M1), m(M1)                       % 後者値
      ; M = pred(M1), m(M1)                       % 前者値
      ; M = iszero(M1), m(M1)                     % ゼロ判定
      .
n(N) :-                                           % 数値:
        N = 0                                     % ゼロ
      ; N = succ(N1), n(N1)                       % 後者値
      .
v(V) :-                                           % 値:
        V = true                                  % 定数真
      ; V = false                                 % 定数偽
      ; V = NV, n(NV)                             % 数値
      .

% 評価 M ==> M_

if(true, M2, _)  ==> M2.
if(false, _, M3) ==> M3.
if(M1, M2, M3)   ==> if(M1_, M2, M3) where M1 ==> M1_.
succ(M1)         ==> succ(M1_)       where M1 ==> M1_.
pred(0)          ==> 0.
pred(succ(N1))   ==> N1              where n(N1).
pred(M1)         ==> pred(M1_)       where M1 ==> M1_.
iszero(0)        ==> true.
iszero(succ(N1)) ==> false           where n(N1).
iszero(M1)       ==> iszero(M1_)     where M1 ==> M1_.

M               ==>> M_              where M  ==> M1, M1 ==>> M_.
M               ==>> M.

run(eval(M), Γ, Γ) :- !, m(M), !, M ==>> M_, !, writeln(M_).
run(Ls)            :- foldl(run, Ls, [], _).

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
