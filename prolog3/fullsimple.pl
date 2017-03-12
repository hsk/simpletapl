:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | true | false | zero. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).        % 識別子:
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A|list(A)].             % リスト

t ::=                       % 型:
      bool                  % ブール値型
    | nat                   % 自然数型
    | unit                  % Unit型
    | float                 % 浮動小数点数型
    | string                % 文字列型
    | x                     % 型変数
    | arr(t,t)              % 関数の型
    | record(list(l:t))     % レコードの型
    | variant(list(x:t))    % バリアント型
    .
m ::=                       % 項:
      true                  % 真
    | false                 % 偽
    | if(m,m,m)             % 条件式
    | zero                  % ゼロ
    | succ(m)               % 後者値
    | pred(m)               % 前者値
    | iszero(m)             % ゼロ判定
    | unit                  % 定数unit
    | floatl                % 浮動小数点数値
    | timesfloat(m,m)       % 浮動小数点乗算
    | stringl               % 文字列定数
    | x                     % 変数
    | fn(x,t,m)             % ラムダ抽象
    | app(m,m)              % 関数適用
    | let(x,m,m)            % let束縛
    | fix(m)                % mの不動点
    | inert(t)
    | as(m,t)               % 型指定
    | record(list(l=m))     % レコード
    | proj(m,l)             % 射影
    | case(m,list(x=(x,m))) % 場合分け
    | tag(x,m,t)            % タグ付け
    .
n ::=                       % 数値:
      zero                  % ゼロ
    | succ(n)               % 後者値
    .
v ::=                       % 値:
      true                  % 真
    | false                 % 偽
    | n                     % 数値
    | unit                  % 定数unit
    | floatl                % 浮動小数点数値
    | stringl               % 文字列定数
    | fn(x,t,m)             % ラムダ抽象
    | record(list(l=v))     % レコード
    | tag(x,v,t)            % タグ付け
    .

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,record(Mf),record(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,variant(Mf),variant(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
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
subst(J,M,tag(L,M1,T1), tag(L,M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,case(M,Cases), case(M_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

gett(Γ,X,T) :- member(X:T,Γ).
gett(Γ,X,T) :- member(X-_:T,Γ).
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
eval1(Γ,X,M) :- x(X),member(X-M:_,Γ).
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
eval1(Γ,tag(L,M1,T),tag(L,M1_,T)) :- eval1(Γ,M1,M1_).
eval1(Γ,case(tag(L,V11,_),Bs),M_) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(Γ,case(M1,Bs),case(M1_, Bs)) :- eval1(Γ,M1,M1_).

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

gettabb(Γ,X,T) :- member(X=T,Γ).
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
teq2(Γ,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Γ,S,T),Sf,Tf).

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
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X:T1|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), teq(Γ,T11,T2).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X:T1|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),teq(Γ,T12,T11).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- typeof(Γ,M1,T1),teq(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),simplify(Γ,T1,record(Tf)),member(L:T,Tf).
typeof(Γ,tag(Li, Mi, T), T) :- simplify(Γ,T,variant(Tf)),member(Li:Te,Tf),typeof(Γ,Mi, T_),teq(Γ,T_,Te).
typeof(Γ,case(M, Cases), T1) :-
    typeof(Γ,M,T),simplify(Γ,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi:Ti|Γ],Mi,Ti_)),Cases,[T1|RestT]),
    maplist([Tt]>>teq(Γ,Tt,T1), RestT).
typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show(Γ,X-type) :- format('~w\n',[X]).
show(Γ,X-M:T)  :- format('~w : ~w\n',[X,T]).
show(Γ,X=T)        :- format('~w :: *\n',[X]).
show(Γ,X:T)        :- format('~w : ~w\n',[X,T]).

run(type(X),Γ,[X-type|Γ]) :- x(X),show(Γ,X-type).
run(type(X)=T,Γ,[X=T|Γ]) :- x(X),t(T),show(Γ,X=T).
run(X:T,Γ,[X:T|Γ]) :- x(X),t(T),show(Γ,X:T).
run(X=M,Γ,[X-M_:T|Γ]) :- x(X),m(M),typeof(Γ,M,T),eval(Γ,M,M_),show(Γ,X-M_:T).
run(X:T=M,Γ,[X-M:T|Γ]) :- x(X),t(T),m(M),typeof(Γ,M,T_),teq(Γ,T_,T),eval(Γ,M,M_),show(Γ,X-M_:T).
run(M,Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

%  lambda x:<a:Bool,b:Bool>. x;
:- run([fn(x,variant([a:bool,b:bool]),x)]).
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
% {x=true, y=false};
:- run([record([x=true,y=false])]).
% {x=true, y=false}.x;
:- run([proj(record([x=true,y=false]),x)]).
% {true, false};
:- run([record([1=true,2=false])]).
% {true, false}.1;
:- run([proj(record([1=true,2=false]),1)]).
% lambda x:Bool. x;
:- run([fn(x,bool,x)]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
            fn(x,bool, if(x, false, true)))]).
% lambda x:Nat. succ x;
:- run([fn(x,nat, succ(x))]).
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([app(fn(x,nat, succ(succ(x))),succ(zero) )]).
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T')=arr(nat,nat),
        fn(f,'T',fn(x,nat,app(f,app(f,x))))]).
% a = let x = succ 2 in succ x;
% a;
:- run([a=let(x,succ(succ(succ(zero))),succ(x)),
        a]).
% <a=0> as <a:nat,b:bool>
:- run([tag(a,pred(succ(zero)),variant([a:nat,b:bool]))]).
% case <a=0> as <a:nat,b:bool> of
% <a=n> ==> isZero(n)
% | <b=b> ==> b;
:- run([case(tag(a,pred(succ(zero)),variant([a:nat,b:bool])),[a=(n,iszero(n)),b=(b,b)])]).
:- halt.
