% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

m ::=           % 項:
      true      % 真
    | false     % 偽
    | if(m,m,m) % 条件式
    | zero      % ゼロ
    | succ(m)   % 後者値
    | pred(m)   % 前者値
    | iszero(m) % ゼロ判定
    .
n ::=           % 数値:
      zero      % ゼロ
    | succ(n)   % 後者値
    .
v ::=           % 値:
      true      % 真
    | false     % 偽
    | n         % 数値
    .

% ------------------------   EVALUATION  ------------------------

eval1(if(true,M2,_), M2).
eval1(if(false,_,M3), M3).
eval1(if(M1,M2,M3), if(M1_, M2, M3)) :- eval1(M1,M1_).
eval1(succ(M1),succ(M1_))            :- eval1(M1,M1_).
eval1(pred(zero), zero).
eval1(pred(succ(N1)), N1)            :- n(N1).
eval1(pred(M1), pred(M1_))           :- eval1(M1,M1_).
eval1(iszero(zero), true).
eval1(iszero(succ(N1)), false)       :- n(N1).
eval1(iszero(M1), iszero(M1_))       :- eval1(M1,M1_).

eval(M,M_)                           :- eval1(M,M1), eval(M1,M_).
eval(M,M).

% ------------------------   MAIN  ------------------------

run(M,Γ,Γ) :- !,m(M),!,eval(M,M_),!, writeln(M_).
run(Ls)          :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([true]).
:- run([if(false,true,false)]).
:- run([zero]).
:- run([succ(pred(zero))]).
:- run([iszero(pred(succ(succ(zero))))]).
:- run([iszero(pred(pred(succ(succ(zero)))))]).
:- run([iszero(zero)]).
:- run([if(zero,succ(pred(zero)),zero)]).
:- run([if(zero,succ(succ(zero)),zero)]).
:- run([if(zero,succ(pred(succ(zero))),zero)]).
:- halt.
