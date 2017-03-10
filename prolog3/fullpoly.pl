:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | true | false | zero. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).        % 識別子:
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A|list(A)].             % リスト

t ::=                   % 型:
      bool              % ブール値型
    | nat               % 自然数型
    | unit              % Unit型
    | float             % 浮動小数点数型
    | string            % 文字列型
    | x                 % 型変数
    | arr(t,t)          % 関数の型
    | record(list(l:t)) % レコードの型
    | some(x,t)         % 存在型
    | all(x,t)          % 全称型
    .
m ::=                   % 項:
      true              % 真
    | false             % 偽
    | if(m,m,m)         % 条件式
    | zero              % ゼロ
    | succ(m)           % 後者値
    | pred(m)           % 前者値
    | iszero(m)         % ゼロ判定
    | unit              % 定数unit
    | floatl            % 浮動小数点数値
    | timesfloat(m,m)   % 浮動小数点乗算
    | stringl           % 文字列定数
    | x                 % 変数
    | fn(x,t,m)         % ラムダ抽象
    | app(m,m)          % 関数適用
    | let(x,m,m)        % let束縛
    | fix(m)            % mの不動点
    | inert(t)
    | as(m,t)           % 型指定
    | record(list(l=m)) % レコード
    | proj(m,l)         % 射影
    | as(m,t)           % 型指定
    | pack(t,m,t)       % パッケージ化
    | unpack(x,x,m,m)   % アンパッケージ化
    | tfn(x,m)          % 型抽象
    | tapp(m,t)         % 型適用
    .
n ::=                   % 数値:
      zero              % ゼロ
    | succ(n)           % 後者値
    .
v ::=                   % 値:
      true              % 真
    | false             % 偽
    | n                 % 数値
    | unit              % 定数unit
    | floatl            % 浮動小数点数値
    | stringl           % 文字列定数
    | fn(x,t,m)         % ラムダ抽象
    | record(list(l=v)) % レコード
    | pack(t,v,t)       % パッケージ化
    | tfn(x,m)          % 型抽象
    .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,record(Mf),record(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,some(TX,T2),some(TX,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,all(TX,T2),all(TX,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,unit,unit).
subst(J,M,F1,F1) :- float(F1).
subst(J,M,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,X,X) :- string(X).
subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,fix(M1), fix(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,inert(T1), inert(T1)).
subst(J,M,as(M1,T1), as(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,pack(T1,M2,T3),pack(T1,M2_,T3)) :- subst(J,M,M2,M2_).
subst(J,M,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- subst2(X,J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,tfn(TX,M2),tfn(TX,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

tmsubst(J,S,true,true).
tmsubst(J,S,false,false).
tmsubst(J,S,if(M1,M2,M3),if(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,zero,zero).
tmsubst(J,S,succ(M1),succ(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,pred(M1),pred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,iszero(M1),iszero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,M,unit,unit).
tmsubst(J,M,F1,F1) :- float(F1).
tmsubst(J,M,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- tmsubst(J,M,M1,M1_), tmsubst(J,M,M2,M2_).
tmsubst(J,M,X,X) :- string(X).
tmsubst(J,S,X,X) :- x(X).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X,M1,M2),let(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,M,fix(M1), fix(M1_)) :- tmsubst(J,M,M1,M1_).
tmsubst(J,M,inert(T1), inert(T1)).
tmsubst(J,S,as(M1,T1),as(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>tmsubst(J,M,Mi,Mi_),Mf,Mf_).
tmsubst(J,M,proj(M1,L),proj(M1_,L)) :- tmsubst(J,M,M1,M1_).
tmsubst(J,M,pack(T1,M2,T3),pack(T1_,M2_,T3_)) :- tsubst(J,S,T1,T1_),tmsubst(J,M,M2,M2_),tsubst(J,S,T3,T3_).
tmsubst(J,M,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- tmsubst2(TX,J,M,M1,M1_),tmsubst2(TX,J,M,M2,M2_).
tmsubst(J,S,tfn(TX,M2),tfn(TX,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
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
eval1(Γ,timesfloat(F1,F2),F3) :- float(F1),float(F2),F3 is F1 * F2.
eval1(Γ,timesfloat(V1,M2),timesfloat(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,timesfloat(M1,M2),timesfloat(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,X,M) :- x(X),getb(Γ,X,bMAbb(M,_)).
eval1(Γ,app(fn(X,_,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,let(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,let(X,M1,M2),let(X,M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,fix(fn(X,T,M12)),M12_) :- subst(X,fix(fn(X,T,M12)),M12,M12_).
eval1(Γ,fix(M1),fix(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,as(V1,_), V1) :- v(V1).
eval1(Γ,as(M1,T), as(M1_,T)) :- eval1(Γ,M1,M1_).
eval1(Γ,record(Mf),record(Mf_)) :- e(Mf,M,Mf_,M_),eval1(Γ,M,M_).
eval1(Γ,proj(record(Mf),L),M) :- member(L=M,Mf).
eval1(Γ,proj(M1,L),proj(M1_, L)) :- eval1(Γ,M1,M1_).
eval1(Γ,pack(T1,M2,T3),pack(T1,M2_, T3)) :- eval1(Γ,M2,M2_).
eval1(Γ,unpack(_,X,pack(T11,V12,_),M2),M) :- v(V12),subst(X,V12,M2,M2_),tmsubst(X,T11,M2_,M).
eval1(Γ,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,tapp(tfn(X,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,tapp(M1,T2),tapp(M1_,T2)) :- eval1(Γ,M1,M1_).
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T)).
compute(Γ,X,T) :- x(X),gettabb(Γ,X,T).

simplify(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify(Γ,T,T).

teq(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_),teq2(Γ,S_,T_).
teq2(Γ,bool,bool).
teq2(Γ,nat,nat).
teq2(Γ,unit,unit).
teq2(Γ,float,float).
teq2(Γ,string,string).
teq2(Γ,X,T) :- x(X),gettabb(Γ,X,S),teq(Γ,S,T).
teq2(Γ,S,X) :- x(X),gettabb(Γ,X,T),teq(Γ,S,T).
teq2(Γ,X,X) :- x(X).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).
teq2(Γ,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Γ,S,T)), Tf).
teq2(Γ,all(TX1,S2),all(_,T2)) :- teq([TX1-bName|Γ],S2,T2).
teq2(Γ,some(TX1,S2),some(_,T2)) :- teq([TX1-bName|Γ],S2,T2).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T2) :- typeof(Γ,M1,T1),teq(Γ,T1,bool),typeof(Γ,M2,T2),typeof(Γ,M3,T3), teq(Γ,T2,T3).
typeof(Γ,zero,nat).
typeof(Γ,succ(M1),nat) :- typeof(Γ,M1,T1),teq(Γ,T1,nat),!.
typeof(Γ,pred(M1),nat) :- typeof(Γ,M1,T1),teq(Γ,T1,nat),!.
typeof(Γ,iszero(M1),bool) :- typeof(Γ,M1,T1),teq(Γ,T1,nat),!.
typeof(Γ,unit,unit).
typeof(Γ,F1,float) :- float(F1).
typeof(Γ,timesfloat(M1,M2),float) :- typeof(Γ,M1,T1),teq(Γ,T1,float),typeof(Γ,M2,T2),teq(Γ,T2,float).
typeof(Γ,X,string) :- string(X).
typeof(Γ,X,T) :- x(X),gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), teq(Γ,T11,T2).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),teq(Γ,T12,T11).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- typeof(Γ,M1,T1),teq(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),simplify(Γ,T1,record(Tf)),member(L:T,Tf).
typeof(Γ,pack(T1,M2,T),T) :- simplify(Γ,T,some(Y,T2)),typeof(Γ,M2,S2),tsubst(Y,T1,T2,T2_),teq(Γ,S2,T2_).
typeof(Γ,unpack(TX,X,M1,M2),T2) :- typeof(Γ,M1,T1),
      simplify(Γ,T1,some(_,T11)),typeof([X-bVar(T11),(TX-bTVar)|Γ],M2,T2).
typeof(Γ,tfn(TX,M2),all(TX,T2)) :- typeof([TX-bTVar|Γ],M2,T2).
typeof(Γ,tapp(M1,T2),T12_) :- typeof(Γ,M1,T1),simplify(Γ,T1,all(X,T12)),tsubst(X,T2,T12,T12_).

show(Γ,X,bName) :- format('~w\n',[X]).
show(Γ,X,bVar(T)) :- format('~w : ~w\n',[X,T]).
show(Γ,X,bTVar) :- format('~w\n',[X]).
show(Γ,X,bMAbb(M,T)) :- format('~w : ~w\n',[X,T]).
show(Γ,X,bTAbb(T)) :- format('~w :: *\n',[X]).

run(type(X),Γ,[X-bTVar|Γ]) :- show(Γ,X,bTVar).
run(type(X)=T,Γ,[X-bTAbb(T)|Γ]) :- show(Γ,X,bTAbb(T)).
run(X:T,Γ,[X-bVar(T)|Γ]) :- show(Γ,X,bVar(T)).
run(X:T=M,Γ,[X-bMAbb(M_,T)|Γ]) :- typeof(Γ,M,T_),teq(Γ,T_,T),eval(Γ,M,M_),show(Γ,X,bMAbb(M_,T)).
run(X=M,Γ,[X-bMAbb(M_,T)|Γ]) :- typeof(Γ,M,T),eval(Γ,M,M_),show(Γ,X,bMAbb(M_,T)).
run(someBind(TX,X,M),Γ,[X-bMAbb(T12,some(TBody)),TX-bTVar|Γ]) :-
  typeof(Γ,M,T),simplify(Γ,T,some(_,TBody)),eval(Γ,M,pack(_,T12,_)),writeln(TX),write(X),write(' : '),writeln(TBody).
run(someBind(TX,X,M),Γ,[X-bVar(TBody),TX-bTVar|Γ]) :-
  typeof(Γ,M,T),simplify(Γ,T,some(_,TBody)),writeln(TX),write(X),write(' : '),writeln(TBody).
run(M,Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% "hello";
:- run(["hello"]).
% unit;
:- run([unit]).
% lambda x:A. x;
:- run([fn(x,'A',x)]).
% let x=true in x;
:- run([let(x,true,x)]).
% timesfloat 2.0 3.14159;
:- run([timesfloat(2.0,3.14159)]).
% lambda x:Bool. x;
:- run([fn(x,bool,x)]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
            fn(x,bool, if(x, false, true)))]).
% lambda x:Nat. succ x;
:- run([fn(x,nat, succ(x))]).
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([app(fn(x,nat, succ(succ(x))),succ(zero))]).
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T')=arr(nat,nat),
        fn(f,'T',fn(x,nat,app(f,app(f,x))))]).
% lambda X. lambda x:X. x;
:- run([tfn('X',fn(x,'X',x))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([tapp(tfn('X',fn(x,'X',x)),all('X',arr('X','X')))]).
% {*Nat, lambda x:Nat. succ x} as {Some X, X->Nat};
:- run([pack(nat,fn(x,nat,succ(x)),some('X',arr('X',nat)))]).
% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([pack(all('Y','Y'),fn(x,all('Y','Y'),x),some('X',arr('X','X')))]).
% {x=true, y=false};
:- run([record([x=true,y=false])]).
% {x=true, y=false}.x;
:- run([proj(record([x=true,y=false]),x)]).
% {true, false};
:- run([record([1=true,2=false])]).
% {true, false}.1;
:- run([proj(record([1=true,2=false]),1)]).
% {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}};
:- run([pack(nat,record([c=zero,f=fn(x,nat,succ(x))]),
         some('X',record([c:'X',f:arr('X',nat)])))]).
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);

:- run([unpack('X',ops,pack(nat,record([c=zero,f=fn(x,nat,succ(x))]),some('X',record([c:'X',f:arr('X',nat)]))),app(proj(ops,f),proj(ops,c)))]).

:- halt.
