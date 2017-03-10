:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | true | false | zero. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X). % 識別子:
t ::=                              % 型:
      bool                         % ブール値型
    | nat                          % 自然数型
    | x                            % 型変数
    | arr(t,t)                     % 関数の型
    .
m ::=                              % 項:
      true                         % 真
    | false                        % 偽
    | if(m,m,m)                    % 条件式
    | zero                         % ゼロ
    | succ(m)                      % 後者値
    | pred(m)                      % 前者値
    | iszero(m)                    % ゼロ判定
    | x                            % 変数
    | fn(x,t,m)                    % ラムダ抽象
    | app(m,m)                     % 関数適用
    .
n ::=                              % 数値:
      zero                         % ゼロ
    | succ(n)                      % 後者値
    .
v ::=                              % 値:
      true                         % 真
    | false                        % 偽
    | n                            % 数値
    | fn(x,t,m)                    % ラムダ抽象
    .

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(Γ,M)),fail.
eval1(Γ,if(true,M2,_),M2).
eval1(Γ,if(false,_,M3),M3).
eval1(Γ,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(Γ,M1,M1_).
eval1(Γ,succ(M1),succ(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,pred(zero),zero).
eval1(Γ,pred(succ(N1)),N1) :- n(N1).
eval1(Γ,pred(M1),pred(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,iszero(zero),true).
eval1(Γ,iszero(succ(N1)),false) :- n(N1).
eval1(Γ,iszero(M1),iszero(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(Γ,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_,M2)) :- eval1(Γ,M1,M1_).
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1),eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3), T2) :- typeof(Γ,M1,bool), typeof(Γ,M2, T2), typeof(Γ,M3, T2).
typeof(Γ,zero,nat).
typeof(Γ,succ(M1),nat) :- typeof(Γ,M1,nat).
typeof(Γ,pred(M1),nat) :- typeof(Γ,M1,nat).
typeof(Γ,iszero(M1),bool) :- typeof(Γ,M1,nat).
typeof(Γ,X,T) :- x(X),gett(Γ, X, T).
typeof(Γ,fn(X,T1,M2), arr(T1, T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,arr(T11,T12)), typeof(Γ,M2,T11).
%typeof(Γ,M,_) :- writeln(error:typeof(M)),halt.

% ------------------------   MAIN  ------------------------

show(Γ,bName,'').
show(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(X : T,Γ,[X-bVar(T)|Γ]) :- show(Γ,bVar(T),S),write(X),writeln(S).
run(eval(M),Γ,Γ) :- !,m(M),!,eval(Γ,M,M_),!, typeof(Γ,M_,T),!, writeln(M_:T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([eval(fn(x,'A',x))]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,x))]).
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x, false, true)))) ]). 
% lambda x:Nat. succ x;
:- run([eval(fn(x,nat, succ(x)))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(app(fn(x,nat, succ(succ(x))),succ(zero) )) ]). 
:- halt.
