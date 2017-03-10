:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | true | false | zero | error. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).        % 識別子:
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(integer).                          % 整数
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A|list(A)].             % リスト

k ::=                   % カインド:
      *                 % 真の型のカインド
    | kArr(k,k)         % 演算子のカインド
    .
t ::=                   % 型:
      bool              % ブール値型
    | nat               % 自然数型
    | unit              % Unit型
    | float             % 浮動小数点数型
    | string            % 文字列型
    | x                 % 型変数
    | arr(t,t)          % 関数の型
    | record(list(l:t)) % レコードの型
    | ref(t)            % 参照セルの型
    | all(x,k,t)        % 全称型
    | some(x,k,t)       % 存在型
    | abs(x,k,t)        % 型抽象
    | app(t,t)          % 関数適用
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
    | loc(integer)      % ストアでの位置
    | ref(m)            % 参照の生成
    | deref(m)          % 参照先の値の取り出し
    | assign(m,m)       % 破壊的代入
    | pack(t,m,t)       % パッケージ化
    | unpack(x,x,m,m)   % アンパッケージ化
    | tfn(x,k,m)        % 型抽象
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
    | loc(integer)      % ストアでの位置
    | pack(t,v,t)       % パッケージ化
    | tfn(x,t,m)        % 型抽象
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
tsubst(J,S,ref(T1),ref(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,all(TX,K1,T2),all(TX,K1,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,some(TX,K1,T2),some(TX,K1,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,abs(TX,K1,T2),abs(TX,K1,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,app(TX,T1,T2),app(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
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
subst(J,M,ref(M1), ref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,deref(M1), deref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,assign(M1,M2), assign(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,loc(L), loc(L)).
subst(J,M,tfn(TX,K1,M2),tfn(TX,K1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,pack(T1,M2,T3),pack(T1,M2_,T3)) :- subst(J,M,M2,M2_).
subst(J,M,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- subst2(X,J,M,M1,M1_),subst2(X,J,M,M2,M2_).
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
tmsubst(J,S,unit,unit).
tmsubst(J,S,F1,F1) :- float(F1).
tmsubst(J,S,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,X,X) :- string(X).
tmsubst(J,S,X,X) :- x(X).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X,M1,M2),let(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,fix(M1), fix(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,inert(T1), inert(T1)).
tmsubst(J,S,as(M1,T1),as(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>tmsubst(J,S,Mi,Mi_),Mf,Mf_).
tmsubst(J,S,proj(M1,L),proj(M1_,L)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,ref(M1),ref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,deref(M1),deref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,assign(M1,M2),assign(M1_,M2_)) :- tmsubst(J,S,M2,M2_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,loc(L),loc(L)).
tmsubst(J,S,tfn(TX,K1,M2),tfn(TX,K1,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst(J,S,pack(T1,M2,T3),pack(T1_,M2_,T3_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_),tsubst(J,S,T3,T3_).
tmsubst(J,S,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).

gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,some(T))).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

extendstore(St,V1,Len,St_) :- length(St,Len),append(St,[V1],St_).
lookuploc(St,L,R) :- nth0(L,St,R).
updatestore([_|St],0,V1,[V1|St]).
updatestore([V|St],N1,V1,[V|St_]) :- N is N1 - 1, updatestore(St,N,V1,St_).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

eval1(Γ,St,if(true,M2,M3),M2,St).
eval1(Γ,St,if(false,M2,M3),M3,St).
eval1(Γ,St,if(M1,M2,M3),if(M1_,M2,M3),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,succ(M1),succ(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,pred(zero),zero,St).
eval1(Γ,St,pred(succ(NV1)),NV1,St) :- n(NV1).
eval1(Γ,St,pred(M1),pred(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,iszero(zero),true,St).
eval1(Γ,St,iszero(succ(NV1)),false,St) :- n(NV1).
eval1(Γ,St,iszero(M1),iszero(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,timesfloat(F1,F2),F3,St) :- float(F1),float(F2),F3 is F1 * F2.
eval1(Γ,St,timesfloat(F1,M2),timesfloat(F1,M2_),St_) :- float(F1), eval1(Γ,St,M2,M2_).
eval1(Γ,St,timesfloat(M1,M2),timesfloat(M1_,M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,X,M,St) :- x(X),getb(Γ,X,bMAbb(M,_)).
eval1(Γ,St,app(fn(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,St,app(V1,M2),app(V1, M2_),St_) :- v(V1), eval1(Γ,St,M2,M2_,St_).
eval1(Γ,St,app(M1,M2),app(M1_, M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,let(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,St,let(X,M1,M2),let(X,M1_,M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,fix(fn(X,T11,M12)),M,St) :- subst(X,fix(fn(X,T11,M12)),M12,M).
eval1(Γ,St,fix(M1),fix(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,as(V1,_), V1,St) :- v(V1).
eval1(Γ,St,as(M1,T), as(M1_,T),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,record(Mf),record(Mf_),St_) :- e(Mf,M,Mf_,M_),eval1(Γ,St,M,M_,St_).
eval1(Γ,St,proj(record(Mf),L),M,St) :- member(L=M,Mf).
eval1(Γ,St,proj(M1,L),proj(M1_, L),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(Γ,St,ref(M1),ref(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(Γ,St,deref(M1),deref(M1_),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(Γ,St,assign(V1,M2),assign(V1, M2_),St_) :- v(V1), eval1(Γ,St,M2,M2_,St_).
eval1(Γ,St,assign(M1,M2),assign(M1_, M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,tapp(tfn(X,K,M11),T2),M11_,St_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,St,tapp(M1,T2),tapp(M1_,T2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,pack(T1,M2,T3),pack(T1,M2_,T3),St_) :- eval1(Γ,St,M2,M2_,St_).
eval1(Γ,St,unpack(_,X,pack(T11,V12,_),M2),M,St) :- v(V12),subst(X,V12,M2,M2_),tmsubst(X,T11,M2_,M).
eval1(Γ,St,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2),St_) :- eval1(St,Γ,M1,M1_,St_).
eval(Γ,St,M,M_,St_) :- eval1(Γ,St,M,M1,St1),eval(Γ,St1,M1,M_,St_).
eval(Γ,St,M,M,St).

evalbinding(Γ,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(Γ,St,M,M_,St_).
evalbinding(Γ,St,Bind,Bind,St).

% ------------------------   KINDING  ------------------------

gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T,_)).
compute(Γ,X,T) :- x(X),gettabb(Γ,X,T).
compute(Γ,app(abs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(Γ,app(T1,T2),T_) :- simplify(Γ,T1,T1_),simplify2(Γ,app(T1_,T2),T_).
simplify(Γ,T,T_) :- simplify2(Γ,T,T_).
simplify2(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify2(Γ,T,T).

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
teq2(Γ,ref(S),ref(T)) :- teq(Γ,S,T).
teq2(Γ,all(TX1,K1,S2),all(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,some(TX1,K1,S2),some(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,abs(TX1,K1,S2),abs(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,app(S1,S2),app(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).


kindof(Γ,T,K) :- kindof1(Γ,T,K),!.
kindof(Γ,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(Γ,X,*) :- x(X),\+member(X-_,Γ).
kindof1(Γ,X,K) :- x(X),getb(Γ,X,bTVar(K)),!.
kindof1(Γ,X,K) :- x(X),!,getb(Γ,X,bTAbb(_,some(K))).
kindof1(Γ,arr(T1,T2),*) :- !,kindof(Γ,T1,*),kindof(Γ,T2,*).
kindof1(Γ,record(Tf),*) :- maplist([L:S]>>kindof(Γ,S,*),Tf).
kindof1(Γ,all(TX,K1,T2),*) :- !,kindof([TX-bTVar(K1)|Γ],T2,*).
kindof1(Γ,some(TX,K1,T2),*) :- !,kindof([TX-bTVar(K1)|Γ],T2,*).
kindof1(Γ,abs(TX,K1,T2),kArr(K1,K)) :- !,kindof([TX-bTVar(K1)|Γ],T2,K).
kindof1(Γ,app(T1,T2),K12) :- !,kindof(Γ,T1,kArr(K11,K12)),kindof(Γ,T2,K11).
kindof1(Γ,T,*).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T2) :- typeof(Γ,M1,T1),teq(Γ,T1,bool),typeof(Γ,M2,T2),typeof(Γ,M3,T3), teq(Γ,T2,T3).
typeof(Γ,zero,nat).
typeof(Γ,succ(M1),nat) :- typeof(Γ,M1,T1),teq(Γ,T1,nat).
typeof(Γ,pred(M1),nat) :- typeof(Γ,M1,T1),teq(Γ,T1,nat).
typeof(Γ,iszero(M1),bool) :- typeof(Γ,M1,T1),teq(Γ,T1,nat).
typeof(Γ,unit,unit).
typeof(Γ,F1,float) :- float(F1).
typeof(Γ,timesfloat(M1,M2),float) :- typeof(Γ,M1,T1),teq(Γ,T1,float),typeof(Γ,M2,T2),teq(Γ,T2,float).
typeof(Γ,X,string) :- string(X).
typeof(Γ,X,T) :- x(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- kindof(Γ,T1,*),typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), teq(Γ,T11,T2).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),teq(Γ,T12,T11).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- kindof(Γ,T,*),typeof(Γ,M1,T1),teq(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),simplify(Γ,T1,record(Tf)),member(L:T,Tf).
typeof(Γ,ref(M1),ref(T1)) :- typeof(Γ,M1,T1).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), simplify(Γ,T,ref(T1)).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), simplify(Γ,T,ref(T1)),typeof(Γ,M2,T2),teq(Γ,T2,T1).
typeof(Γ,pack(T1,M2,T),T) :- kindof(Γ,T,*),simplify(Γ,T,some(Y,K1,T2)),
    kindof(Γ,T1,K1),
    typeof(Γ,M2,S2),tsubst(Y,T1,T2,T2_),teq(Γ,S2,T2_).
typeof(Γ,unpack(TX,X,M1,M2),T2) :- typeof(Γ,M1,T1),
      simplify(Γ,T1,some(_,K,T11)),typeof([X-bVar(T11),(TX-bTVar(K))|Γ],M2,T2).
typeof(Γ,tfn(TX,K1,M2),all(TX,K1,T2)) :- typeof([TX-bTVar(K1)|Γ],M2,T2).
typeof(Γ,tapp(M1,T2),T12_) :- kindof(Γ,T2,K2),typeof(Γ,M1,T1),simplify(Γ,T1,all(X,K2,T12)),tsubst(X,T2,T12,T12_).
typeof(Γ,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).
show_bind(Γ,bTAbb(T,none),R) :- kindof(Γ,T,K), swritef(R,' :: %w',[K]).
show_bind(Γ,bTAbb(T,some(K)),R) :- swritef(R,' :: %w',[K]).
show_bind(Γ,bMAbb(M,none),R) :- typeof(Γ,M,T),swritef(R,' : %w',[T]).
show_bind(Γ,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).

check_bind(Γ,bName,bName).
check_bind(Γ,bTVar(K),bTVar(K)).
check_bind(Γ,bTAbb(T,none),bTAbb(T,some(K))) :- kindof(Γ,T,K).
check_bind(Γ,bTAbb(T,some(K)),bTAbb(T,some(K))) :- kindof(Γ,T,K).
check_bind(Γ,bVar(T),bVar(T)).
check_bind(Γ,bMAbb(M,none), bMAbb(M,some(T))) :- typeof(Γ,M,T).
check_bind(Γ,bMAbb(M,some(T)),bMAbb(M,some(T))) :- typeof(Γ,M,T1), teq(Γ,T1,T).

check_someBind(TBody,pack(_,T12,_),bMAbb(T12,some(TBody))).
check_someBind(TBody,_,bVar(TBody)).

run(type(X)=T,(Γ,St),([X-Bind_|Γ],St_)) :-
    check_bind(Γ,bTAbb(T,none),Bind1),
    evalbinding(Γ,St,Bind1,Bind_,St_),
    write(X),show_bind(Γ,Bind_,R),writeln(R).
run(bind(X,Bind),(Γ,St),([X-Bind_|Γ],St_)) :-
    check_bind(Γ,Bind,Bind1),
    evalbinding(Γ,St,Bind1,Bind_,St_),
    write(X),show_bind(Γ,Bind_,R),writeln(R).
run(someBind(TX,X,M),(Γ,St),([X-B,TX-bTVar(K)|Γ],St_)) :-
    !,typeof(Γ,M,T),
    simplify(Γ,T,some(_,K,TBody)),
    eval(Γ,St,M,M_,St_),
    check_someBind(TBody,M_,B),
    writeln(TX),write(X),write(' : '),writeln(TBody).
run(eval(M),(Γ,St),(Γ,St_)) :-
    !,m(M),!,typeof(Γ,M,T),!,eval(Γ,St,M,M_,St_),!,writeln(M_:T).

run(Ls) :- foldl(run,Ls,([],[]),_).

% ------------------------   TEST  ------------------------

% "hello";
:- run([eval("hello")]).
% unit;
:- run([eval(unit)]).
% lambda x:A. x;
:- run([eval(fn(x,'A',x))]).
% let x=true in x;
:- run([eval(let(x,true,x))]).
% timesfloat 2.0 3.14159;
:- run([eval(timesfloat(2.0,3.14159))]).
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
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T')=arr(nat,nat),
        eval(fn(f,'T',fn(x,nat,app(f,app(f,x)))))]).
% lambda X. lambda x:X. x;
:- run([eval(tfn('X',*,fn(x,'X',x)))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(tapp(tfn('X',*,fn(x,'X',x)),all('X',*,arr('X','X'))))]).

% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([eval(pack(all('Y',*,'Y'),fn(x,all('Y',*,'Y'),x),some('X',*,arr('X','X')) ))]).

% {x=true, y=false};
:- run([eval(record([x=true,y=false])) ]).
% {x=true, y=false}.x;
:- run([eval(proj(record([x=true,y=false]),x)) ]).
% {true, false};
:- run([eval(record([1=true,2=false])) ]).
% {true, false}.1;
:- run([eval(proj(record([1=true,2=false]),1)) ]).
% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
:- run([eval(pack(nat,record([c=zero,f=fn(x,nat,succ(x))]),
         some('X',*,record([c:'X',f:arr('X',nat)]))))]).

% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);
:- run([eval(unpack('X',ops,pack(nat,record([c=zero,f=fn(x,nat,succ(x))]),some('X',*,record([c:'X',f:arr('X',nat)]))),app(proj(ops,f),proj(ops,c))) )]).

:-run([
% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;
type('Pair')=abs('X',*,abs('Y',*,
  all('R',*,arr(arr('X',arr('Y','R')),'R')))),
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;
bind(pair,bMAbb(tfn('X',*,tfn('Y',*,
  fn(x,'X',fn(y,'Y',
    tfn('R',*,
      fn(p,arr('X',arr('Y','R')),
        app(app(p,x),y))))))),none)),
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
bind(fst,bMAbb(tfn('X',*,tfn('Y',*,
  fn(p,app(app('Pair','X'),'Y'),
    app(tapp(p,'X'),
         fn(x,'X',fn(y,'Y',x)) ) ))),none)),
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);
bind(snd,bMAbb(tfn('X',*,tfn('Y',*,
  fn(p,app(app('Pair','X'),'Y'),
    app(tapp(p,'Y'),
         fn(x,'X',fn(y,'Y',y)) ) ))),none)),
% pr = pair [Nat] [Bool] 0 false;
bind(pr,bMAbb(app(app(tapp(tapp(pair,nat),bool),zero),false),none)),
% fst [Nat] [Bool] pr;
eval(app(tapp(tapp(fst,nat),bool),pr)),
% snd [Nat] [Bool] pr;
eval(app(tapp(tapp(snd,nat),bool),pr))
]).

% List = lambda X. All R. (X->R->R) -> R -> R; 

% diverge =
% lambda X.
%   lambda _:Unit.
%   fix (lambda x:X. x);

% nil = lambda X.
%       (lambda R. lambda c:X->R->R. lambda n:R. n)
%       as List X; 

% cons = 
% lambda X.
%   lambda hd:X. lambda tl: List X.
%      (lambda R. lambda c:X->R->R. lambda n:R. c hd (tl [R] c n))
%      as List X; 

% isnil =  
% lambda X. 
%   lambda l: List X. 
%     l [Bool] (lambda hd:X. lambda tl:Bool. false) true; 

% head = 
% lambda X. 
%   lambda l: List X. 
%     (l [Unit->X] (lambda hd:X. lambda tl:Unit->X. lambda _:Unit. hd) (diverge [X]))
%     unit; 

% tail =  
% lambda X.  
%   lambda l: List X. 
%     (fst [List X] [List X] ( 
%       l [Pair (List X) (List X)]
%         (lambda hd: X. lambda tl: Pair (List X) (List X). 
%           pair [List X] [List X] 
%             (snd [List X] [List X] tl)  
%             (cons [X] hd (snd [List X] [List X] tl))) 
%         (pair [List X] [List X] (nil [X]) (nil [X]))))
%     as List X; 

:- halt.
