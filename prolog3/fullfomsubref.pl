:- op(920, xfx, [<:]).
:- op(600, xfy, [::]).
:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | top | true | false | zero | error. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).        % 識別子:
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(integer).                          % 整数
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A|list(A)].             % リスト

k ::=                                     % カインド:
      *                                   % 真の型のカインド
    | kArr(k,k)                           % 演算子のカインド
    .
t ::=                                     % 型:
      bool                                % ブール値型
    | nat                                 % 自然数型
    | unit                                % Unit型
    | float                               % 浮動小数点数型
    | string                              % 文字列型
    | top                                 % 最大の型
    | bot                                 % 最小の型
    | x                                   % 型変数
    | arr(t,t)                            % 関数の型
    | record(list(l:t))                   % レコードの型
    | variant(list(x:t))                  % バリアント型
    | ref(t)                              % 参照セルの型
    | source(t)
    | sink(t)
    | all(x,t,t)                          % 全称型
    | some(x,t,t)                         % 存在型
    | abs(x,k,t)                          % 型抽象
    | app(t,t)                            % 関数適用
    .
m ::=                                     % 項:
      true                                % 真
    | false                               % 偽
    | if(m,m,m)                           % 条件式
    | zero                                % ゼロ
    | succ(m)                             % 後者値
    | pred(m)                             % 前者値
    | iszero(m)                           % ゼロ判定
    | unit                                % 定数unit
    | floatl                              % 浮動小数点数値
    | timesfloat(m,m)                     % 浮動小数点乗算
    | stringl                             % 文字列定数
    | x                                   % 変数
    | fn(x,t,m)                           % ラムダ抽象
    | app(m,m)                            % 関数適用
    | let(x,m,m)                          % let束縛
    | fix(m)                              % mの不動点
    | inert(t)
    | as(m,t)                             % 型指定
    | record(list(l=m))                   % レコード
    | proj(m,l)                           % 射影
    | case(m,list(x=(x,m)))               % 場合分け
    | tag(x,m,t)                          % タグ付け
    | loc(integer)                        % ストアでの位置
    | ref(m)                              % 参照の生成
    | deref(m)                            % 参照先の値の取り出し
    | assign(m,m)                         % 破壊的代入
    | error                               % 実行時エラー
    | try(m,m)                            % エラーの捕捉
    | pack(t,m,t)                         % パッケージ化
    | unpack(x,x,m,m)                     % アンパッケージ化
    | tfn(x,t,m)                          % 型抽象
    | tapp(m,t)                           % 型適用
    .
n ::=                                     % 数値:
      zero                                % ゼロ
    | succ(n)                             % 後者値
    .
v ::=                                     % 値:
      true                                % 真
    | false                               % 偽
    | n                                   % 数値
    | unit                                % 定数unit
    | floatl                              % 浮動小数点数値
    | stringl                             % 文字列定数
    | fn(x,t,m)                           % ラムダ抽象
    | record(list(l=v))                   % レコード
    | tag(x,v,t)                          % タグ付け
    | loc(integer)                        % ストアでの位置
    | pack(t,v,t)                         % パッケージ化
    | tfn(x,t,m)                          % 型抽象
    .

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,top,top).
tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,record(Mf),record(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,variant(Mf),variant(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,ref(T1),ref(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,source(T1),source(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,sink(T1),sink(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,all(TX,T1,T2),all(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,some(TX,T1,T2),some(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,abs(TX,K,T2),abs(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,app(T1,T2),app(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
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
subst(J,M,case(M1,Cases), case(M1_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst(J,M,ref(M1), ref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,deref(M1), deref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,assign(M1,M2), assign(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,loc(L), loc(L)).
subst(J,M,try(M1,M2), try(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,error, error).
subst(J,M,tfn(TX,T,M2),tfn(TX,T,M2_)) :- subst(J,M,M2,M2_).
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
tmsubst(J,S,tag(L,M1,T1), tag(L,M1_,T1_)) :- tmsubst(J,S,M1,M1_), tsubst(J,S,T1,T1_).
tmsubst(J,S,case(M1,Cases), case(M1_,Cases_)) :- tmsubst(J,S,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,S,M1,M1_), Cases,Cases_).
tmsubst(J,S,ref(M1), ref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,deref(M1), deref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,assign(M1,M2), assign(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,loc(L), loc(L)).
tmsubst(J,S,try(M1,M2), try(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,error, error).
tmsubst(J,S,tfn(TX,T1,M2),tfn(TX,T1_,M2_)) :- tsubst2(TX,J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst(J,S,pack(T1,M2,T3),pack(T1_,M2_,T3_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_),tsubst(J,S,T3,T3_).
tmsubst(J,S,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

maketop(*, top).
maketop(kArr(K1,K2),abs('_',K1,K2_)) :- maketop(K2,K2_).

% ------------------------   EVALUATION  ------------------------

extendstore(St,V1,Len,St_) :- length(St,Len),append(St,[V1],St_).
lookuploc(St,L,R) :- nth0(L,St,R).
updatestore([_|St],0,V1,[V1|St]).
updatestore([V|St],N1,V1,[V|St_]) :- N is N1 - 1, updatestore(St,N,V1,St_).

eval_context(if(M1,M2,M3),ME,if(MH,M2,M3),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(succ(M1),ME,succ(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(pred(M1),ME,pred(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(iszero(M1),ME,iszero(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(timesfloat(M1,M2),ME,timesfloat(MH,M2),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(timesfloat(V1,M2),ME,timesfloat(V1,MH),H) :- \+v(M2), eval_context(M1,ME,MH,H).
eval_context(app(M1,M2),ME,app(MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(app(V1,M2),ME,app(V1,MH),H) :- \+v(M2) -> eval_context(M2,ME,MH,H).
eval_context(let(X,M1,M2),ME,let(X,MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(fix(M1),ME,fix(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(as(M1,T),ME,as(MH,T),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(proj(M1,L),ME,proj(MH,L),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(tag(L,M1,T),ME,tag(L,MH,T),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(case(M1,Branches),ME,case(MH,Branches),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(ref(M1),ME,ref(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(deref(M1),ME,deref(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(assign(M1,M2),ME,assign(MH,M2),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(assign(V1,M2),ME,assign(V1,MH),H) :- \+v(M2), eval_context(M2,ME,MH,H).
eval_context(tapp(M1,T),ME,tapp(MH,T),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(pack(T1,M2,T3),ME,pack(T1,MH,T3),H) :- \+v(M2), eval_context(M2,ME,MH,H).
eval_context(unpack(TX,X,M1,M2),ME,unpack(TX,X,MH,M2),H) :- \+v(M1),eval_context(M1,ME,MH,H).
eval_context(record(Mf),ME,record(MH),H) :- \+v(M1), e(Mf,ME,MH,H).
eval_context(try(M1,M2),M1,try(H,M2),H).
eval_context(M1,M1,H,H) :- \+v(M1).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

eval1(Γ,St,if(true,M2,M3),M2,St).
eval1(Γ,St,if(false,M2,M3),M3,St).
eval1(Γ,St,pred(zero),zero,St).
eval1(Γ,St,pred(succ(NV1)),NV1,St) :- n(NV1).
eval1(Γ,St,iszero(zero),true,St).
eval1(Γ,St,iszero(succ(NV1)),false,St) :- n(NV1).
eval1(Γ,St,timesfloat(F1,F2),F3,St) :- float(F1),float(F2),F3 is F1 * F2.
eval1(Γ,St,X,M,St) :- x(X),getb(Γ,X,bMAbb(M,_)).
eval1(Γ,St,app(fn(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,St,let(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,St,fix(fn(X,T11,M12)),M,St) :- subst(X,fix(fn(X,T11,M12)),M12,M).
eval1(Γ,St,as(V1,_), V1,St) :- v(V1).
eval1(Γ,St,proj(record(Mf),L),M,St) :- member(L=M,Mf).
eval1(Γ,St,case(tag(L,V11,_),Bs),M_,St) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(Γ,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(Γ,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(Γ,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(Γ,St,tapp(tfn(X,_,M11),T2),M11_,St_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,St,unpack(_,X,pack(T11,V12,_),M2),M2__,St) :- v(V12),subst(X,V12,M2_),tmsubst(X,T11,M2_,M2__).
eval1(Γ,St,try(error, M2), M2,St).
eval1(Γ,St,try(V1, M2), V1,St) :- v(V1).
eval1(Γ,St,try(M1, M2), try(M1_,M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,error,_,_) :- !, fail.
eval1(Γ,St,M,error,St) :- eval_context(M,error,_,_),!.
eval1(Γ,St,M,M_,St_) :- eval_context(M,ME,M_,H),M\=ME,eval1(Γ,St,ME,H,St_).

eval(Γ,St,M,M_,St_) :- eval1(Γ,St,M,M1,St1),eval(Γ,St1,M1,M_,St_).
eval(Γ,St,M,M,St).

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
teq2(Γ,top,top).
teq2(Γ,X,T) :- x(X),gettabb(Γ,X,S),teq(Γ,S,T).
teq2(Γ,S,X) :- x(X),gettabb(Γ,X,T),teq(Γ,S,T).
teq2(Γ,X,X) :- x(X).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).
teq2(Γ,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Γ,S,T)), Tf).
teq2(Γ,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Γ,S,T),Sf,Tf).
teq2(Γ,ref(S),ref(T)) :- teq(Γ,S,T).
teq2(Γ,source(S),source(T)) :- teq(Γ,S,T).
teq2(Γ,sink(S),sink(T)) :- teq(Γ,S,T).
teq2(Γ,all(TX,S1,S2),all(_,T1,T2)) :- teq(Γ,S1,T1),teq([TX-bName|Γ],S2,T2).
teq2(Γ,some(TX,S1,S2),some(_,T1,T2)) :- teq(Γ,S1,T1),teq([TX-bName|Γ],S2,T2).
teq2(Γ,abs(TX,K1,S2),abs(_,K1,T2)) :- teq([TX-bName|g],S2,T2).
teq2(Γ,app(S1,S2),app(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).

kindof(Γ,T,K) :- kindof1(Γ,T,K),!.
kindof(Γ,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(Γ,X,*) :- x(X),\+member(X-_,Γ).
kindof1(Γ,X,K) :- x(X),getb(Γ,X,bTVar(T)),kindof(Γ,T,K),!.
kindof1(Γ,X,K) :- x(X),!,getb(Γ,X,bTAbb(_,K)).
kindof1(Γ,arr(T1,T2),*) :- !,kindof(Γ,T1,*),kindof(Γ,T2,*).
kindof1(Γ,record(Tf),*) :- maplist([L:S]>>kindof(Γ,S,*),Tf).
kindof1(Γ,variant(Tf),*) :- maplist([L:S]>>kindof(Γ,S,*),Tf).
kindof1(Γ,ref(T),*) :- kindof(Γ,T,*).
kindof1(Γ,source(T),*) :- kindof(Γ,T,*).
kindof1(Γ,sink(T),*) :- kindof(Γ,T,*).
kindof1(Γ,all(TX,T1,T2),*) :- !,kindof([TX-bTVar(T1)|Γ],T2,*).
kindof1(Γ,abs(TX,K1,T2),kArr(K1,K)) :- !,maketop(K1,T1),kindof([TX-bTVar(T1)|Γ],T2,K).
kindof1(Γ,app(T1,T2),K12) :- !,kindof(Γ,T1,kArr(K11,K12)),kindof(Γ,T2,K11).
kindof1(Γ,some(TX,T1,T2),*) :- !,kindof([TX-bTVar(T1)|Γ],T2,*).
kindof1(Γ,T,*).

% ------------------------   SUBTYPING  ------------------------

promote(Γ,X,T) :- x(X),getb(Γ,X,bTVar(T)).
promote(Γ,app(S,T), app(S_,T)) :- promote(Γ,S,S_).

subtype(Γ,S,T) :- teq(Γ,S,T).
subtype(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_), subtype2(Γ,S_,T_).
subtype2(Γ,_,top).
subtype2(Γ,bot,_).
subtype2(Γ,X,T) :- x(X),promote(Γ,X,S),subtype(Γ,S,T).
subtype2(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype2(Γ,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(Γ,S,T)),TF).
subtype2(Γ,variant(SF),variant(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(Γ,S,T)),SF).
subtype2(Γ,ref(S),ref(T)) :- subtype(Γ,S,T),subtype(Γ,T,S).
subtype2(Γ,ref(S),source(T)) :- subtype(Γ,S,T).
subtype2(Γ,source(S),source(T)) :- subtype(Γ,S,T).
subtype2(Γ,ref(S),sink(T)) :- subtype(Γ,T,S).
subtype2(Γ,sink(S),sink(T)) :- subtype(Γ,T,S).
subtype2(Γ,app(T1,T2),T) :- promote(Γ,app(T1,T2),S),subtype(Γ,S,T).
subtype2(Γ,abs(TX,K1,S2),abs(_,K1,T2)) :- maketop(K1,T1),subtype([TX-bTVar(T1)|Γ],S2,T2).
subtype2(Γ,all(TX,S1,S2),all(_,T1,T2)) :-
    subtype(Γ,S1,T1), subtype(Γ,T1,S1),subtype([TX-bTVar(T1)|Γ],S2,T2).
subtype2(Γ,some(TX,S1,S2),some(_,T1,T2)) :-
    subtype(Γ,S1,T1), subtype(Γ,T1,S1),subtype([TX-bTVar(T1)|Γ],S2,T2).

join(Γ,S,T,T) :- subtype(Γ,S,T).
join(Γ,S,T,S) :- subtype(Γ,T,S).
join(Γ,S,T,R) :- simplify(Γ,S,S_),simplify(Γ,T,T_),join2(Γ,S_,T_,R).
join2(Γ,record(SF),record(TF),record(UF_)) :-
    include([L:_]>>member(L:_,TF),SF,UF),
    maplist([L:S,L:T_]>>(member(L:T,TF),join(Γ,S,T,T_)),UF,UF_).
join2(Γ,all(TX,S1,S2),all(_,T1,T2),all(TX,S1,T2_)) :-
      subtype(Γ,S1,T1),subtype(Γ,T1,S1),
      join([TX-bTVar(T1)|Γ],T1,T2,T2_).
join2(Γ,all(TX,S1,S2),all(_,T1,T2),top).
join2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- meet(Γ,S1,T1,S_),join(Γ,S2,T2,T_).
join2(Γ,ref(S),ref(T),ref(S)) :- subtype(Γ,S,T),subtype(Γ,T,S).
join2(Γ,ref(S),ref(T),source(T_)) :- /* Warning: this is incomplete... */ join(Γ,S,T,T_).
join2(Γ,source(S),source(T),source(T_)) :- join(Γ,S,T,T_).
join2(Γ,ref(S),source(T),source(T_)) :- join(Γ,S,T,T_).
join2(Γ,source(S),ref(T),source(T_)) :- join(Γ,S,T,T_).
join2(Γ,sink(S),sink(T),sink(T_)) :- meet(Γ,S,T,T_).
join2(Γ,ref(S),sink(T),sink(T_)) :- meet(Γ,S,T,T_).
join2(Γ,sink(S),ref(T),sink(T_)) :- meet(Γ,S,T,T_).
join2(Γ,_,_,top).

meet(Γ,S,T,S) :- subtype(Γ,S,T).
meet(Γ,S,T,T) :- subtype(Γ,T,S).
meet(Γ,S,T,R) :- simplify(Γ,S,S_),simplify(Γ,T,T_),meet2(Γ,S_,T_,R).
meet2(Γ,record(SF),record(TF),record(UF_)) :-
    maplist([L:S,L:T_]>>(member(L:T,TF),meet(Γ,S,T,T_);T_=S),SF,SF_),
    include([L:_]>>(\+member(L:_,SF)),TF,TF_),
    append(SF_,TF_,UF_).
meet2(Γ,all(TX,S1,S2),all(_,T1,T2),all(TX,S1,T2_)) :-
    subtype(Γ,S1,T1),subtype(Γ,T1,S1),
    meet([TX-bTVar(T1)|Γ],T1,T2,T2_).
meet2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- join(Γ,S1,T1,S_),meet(Γ,S2,T2,T_).
meet2(Γ,ref(S),ref(T),ref(T)) :- subtype(Γ,S,T), subtype(Γ,T,S).
meet2(Γ,ref(S),ref(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,source(S),source(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,ref(S),source(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,source(S),ref(T),source(T_)) :- meet(Γ,S,T,T_).
meet2(Γ,sink(S),sink(T),sink(T_)) :- join(Γ,S,T,T_).
meet2(Γ,ref(S),sink(T),sink(T_)) :- join(Γ,S,T,T_).
meet2(Γ,sink(S),ref(T),sink(T_)) :- join(Γ,S,T,T_).
meet2(Γ,_,_,bot).

% ------------------------   TYPING  ------------------------

lcst(Γ,S,T) :- simplify(Γ,S,S_),lcst2(Γ,S_,T).
lcst2(Γ,S,T) :- promote(Γ,S,S_),lcst(Γ,S_,T).
lcst2(Γ,T,T).

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T) :- typeof(Γ,M1,T1),subtype(Γ,T1,bool),typeof(Γ,M2,T2),typeof(Γ,M3,T3), join(Γ,T2,T3,T).
typeof(Γ,zero,nat).
typeof(Γ,succ(M1),nat) :- typeof(Γ,M1,T1),subtype(Γ,T1,nat).
typeof(Γ,pred(M1),nat) :- typeof(Γ,M1,T1),subtype(Γ,T1,nat).
typeof(Γ,iszero(M1),bool) :- typeof(Γ,M1,T1),subtype(Γ,T1,nat).
typeof(Γ,unit,unit).
typeof(Γ,F1,float) :- float(F1).
typeof(Γ,timesfloat(M1,M2),float) :- typeof(Γ,M1,T1),subtype(Γ,T1,float),typeof(Γ,M2,T2),subtype(Γ,T2,float).
typeof(Γ,X,string) :- string(X).
typeof(Γ,X,T) :- x(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- kindof(Γ,T1,*),typeof([X-bVar(T1)|Γ],M2,T2_),!.
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),!,typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,app(M1,M2),bot) :- !,typeof(Γ,M1,T1),lcst(Γ,T1,bot),typeof(Γ,M2,T2).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),subtype(Γ,T12,T11).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- kindof(Γ,T,*),typeof(Γ,M1,T1),subtype(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf),!.
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),lcst(Γ,T1,record(Tf)),member(L:T,Tf).
typeof(Γ,tag(Li, Mi, T), T) :- simplify(Γ,T,variant(Tf)),member(Li:Te,Tf),typeof(Γ,Mi, T_),subtype(Γ,T_,Te).
typeof(Γ,case(M, Cases), bot) :- typeof(Γ,M,T),lcst(Γ,T,bot),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi)]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases).
typeof(Γ,case(M, Cases), T_) :-
    typeof(Γ,M,T),lcst(Γ,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases,CaseTypes),
    foldl([S,T,U]>>join(G,S,T,U),bot,CaseTypes,T_).
typeof(Γ,ref(M1),ref(T1)) :- typeof(Γ,M1,T1).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), lcst(Γ,T,ref(T1)).
typeof(Γ,deref(M1),bot) :- typeof(Γ,M1,T), lcst(Γ,T,bot).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), lcst(Γ,T,source(T1)).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), lcst(Γ,T,ref(T1)),typeof(Γ,M2,T2),subtype(Γ,T2,T1).
typeof(Γ,assign(M1,M2),bot) :- typeof(Γ,M1,T), lcst(Γ,T,bot),typeof(Γ,M2,_).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), lcst(Γ,T,sink(T1)),typeof(Γ,M2,T2),subtyping(Γ,T2,T1).
typeof(Γ,loc(l),_) :- !,fail.
typeof(Γ,try(M1,M2),T) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),join(Γ,T1,T2,T).
typeof(Γ,error,bot) :- !.
typeof(Γ,pack(T1,M2,T),T) :- kindof(Γ,T,*),simplify(Γ,T,some(Y,TBound,T2)),subtype(Γ,T1,TBound),typeof(Γ,M2,S2),tsubst(Y,T1,T2,T2_),subtype(Γ,S2,T2_).
typeof(Γ,unpack(TX,X,M1,M2),T2) :- typeof(Γ,M1,T1),
      lcst(Γ,T1,some(_,TBound,T11)),typeof([X-bVar(T11),(TX-bTVar(TBound))|Γ],M2,T2).
typeof(Γ,tfn(TX,T1,M2),all(TX,T1,T2)) :- typeof([TX-bTVar(T1)|Γ],M2,T2),!.
typeof(Γ,tapp(M1,T2),T12_) :- typeof(Γ,M1,T1),lcst(Γ,T1,all(X,T11,T12)),subtype(Γ,T2,T11),tsubst(X,T2,T12,T12_).
typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show(Γ,X,bName) :- format('~w\n',[X]).
show(Γ,X,bVar(T)) :- format('~w : ~w\n',[X,T]).
show(Γ,X,bTVar(T)) :- format('~w <: ~w\n',[X,T]). 
show(Γ,X,bMAbb(M,T)) :- format('~w : ~w\n',[X,T]).
show(Γ,X,bTAbb(T,K)) :- format('~w :: ~w\n',[X,K]).

check_someBind(TBody,pack(_,T12,_),bMAbb(T12,TBody)).
check_someBind(TBody,_,bVar(TBody)).

run(X:T,Γ,[X-bVar(T)|Γ])  :- x(X),t(T),show(Γ,X,bVar(T)).
run(X<:K,Γ,[X-bTVar(K)|Γ]) :- x(X),k(K),show(Γ,X,bTVar(K)).
run(type(X::K)=T,(Γ,St),([X-bTAbb(T,K)|Γ],St_)) :- x(X),k(K),t(T),kindof(Γ,T,K), show(Γ,X,bTAbb(T,K)).
run(type(X)=T,(Γ,St),([X-bTAbb(T,K)|Γ],St_)) :- x(X),t(T),kindof(Γ,T,K), show(Γ,X,bTAbb(T,K)).
run(X=M,(Γ,St),([X-bMAbb(M_,T)|Γ],St_)) :- x(X),m(M),typeof(Γ,M,T), eval(Γ,St,M,M_,St_), show(Γ,X,bMAbb(M_,T)).
run(X:T=M,(Γ,St),([X-bMAbb(M_,T)|Γ],St_)) :-
    x(X),t(T),m(M),
    typeof(Γ,M,T1), teq(Γ,T1,T),
    eval(Γ,St,M,M_,St_), show(Γ,X,bMAbb(M_,T)).
run({TX,X}=M,(Γ,St),([X-B,TX-bTVar(K)|Γ],St_)) :-
    x(TX),x(X),m(M),
    !,typeof(Γ,M,T),
    simplify(Γ,T,some(_,K,TBody)),
    eval(Γ,St,M,M_,St_),
    check_someBind(TBody,M_,B),
    format('~w\n~w : ~w\n',[TX,X,TBody]).

run(M,(Γ,St),(Γ,St_)) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,St,M,M_,St_),!,writeln(M_:T).

run(Ls) :- foldl(run,Ls,([],[]),_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([fn(x,bot,x)]).
% lambda x:Bot. x x;
:- run([fn(x,bot,app(x,x))]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([fn(x,variant([a:bool,b:bool]),x)]).
% lambda x:Top. x;
:- run([fn(x,top,x)]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([app(fn(x,top,x),fn(x,top,x))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([app(fn(x,arr(top,top),x),fn(x,top,x))]).
% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([app(fn(r,record([x:arr(top,top)]),app(proj(r,x),proj(r,x))),
            record([x=fn(z,top,z),y=fn(z,top,z)]))]).
% "hello";
:- run(["hello"]).
% unit;
:- run([unit]).
% lambda x:A. x;
% let x=true in x;

% {x=true, y=false};
:- run([record([x=true,y=false])]).
% {x=true, y=false}.x;
:- run([proj(record([x=true,y=false]),x)]).
% {true, false};
:- run([record([1=true,2=false])]).
% {true, false}.1;
:- run([proj(record([1=true,2=false]),1)]).

% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([if(true,record([x=true,y=false,a=false]),record([y=false,x=record([]),b=false]))]).
% try error with true;
:- run([try(error,true)]).
% try if true then error else true with false;
:- run([try(if(true,error,true),false)]).
% try {error,true} with {unit,false};

% timesfloat 2.0 3.14159;
:- run([timesfloat(2.0,3.14159)]).
% lambda X. lambda x:X. x;
:- run([tfn('X',top,fn(x,'X',x))]).
% (lambda X. lambda x:X. x) [Nat];

% lambda X<:Top->Top. lambda x:X. x x;
:- run([tfn('X',arr(top,top),fn(x,'X',app(x,x)))]).

% lambda x:Bool. x;
:- run([fn(x,bool,x)]).
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true);

% if error then true else false;
:- run([if(error,true,false)]).

% error true;
:- run([app(error,true)]).
% (lambda x:Bool. x) error;
:- run([app(fn(x,bool,x),error)]).
% lambda x:Nat. succ x;
:- run([fn(x,nat, succ(x))]).
% (lambda x:Nat. succ (succ x)) (succ 0);
:- run([app(fn(x,nat, succ(succ(x))),succ(zero) )]).
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T')=arr(nat,nat),
        fn(f,'T',fn(x,nat,app(f,app(f,x))))]).


/* Alternative object encodings */


:- run([
% CounterRep = {x: Ref Nat};
type('CounterRep')=record([x:ref(nat)]),
% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}; 
type('SetCounter')=record([get:arr(unit,nat),set:arr(nat,unit),inc:arr(unit,unit)]),
% setCounterClass =
% lambda r:CounterRep.
% lambda self: Unit->SetCounter.
% lambda _:Unit.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (self unit).set (succ((self unit).get unit))} 
%     as SetCounter;
setCounterClass =
    fn(r,'CounterRep',
    fn(self,arr(unit,'SetCounter'),
    fn('_',unit,
    as(record([
        get=fn('_',unit,deref(proj(r,x))),
        set=fn(i,nat,assign(proj(r,x),i)),
        inc=fn('_',unit, app(proj(app(self,unit),set), succ(app(proj(app(self,unit),get),unit)) ))
    ]),'SetCounter' )))),
% newSetCounter = 
% lambda _:Unit.
% let r = {x=ref 1} in
% fix (setCounterClass r) unit;
newSetCounter =
    fn('_',unit,
        let(r,record([x=ref(succ(zero))]),
            app(fix(app(setCounterClass,r)),unit)
        )
    ),
% c = newSetCounter unit;
c = app(newSetCounter, unit),
% c.get unit;
app(proj(c,get),unit),
% InstrCounter = {get:Unit->Nat, 
% set:Nat->Unit, 
% inc:Unit->Unit,
% accesses:Unit->Nat};
type('InstrCounter')=record([
    get:arr(unit,nat),
    set:arr(nat,unit),
    inc:arr(unit,unit),
    accesses:arr(unit,nat)]),
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};
type('InstrCounterRep')=record([x:ref(nat), a:ref(nat)]),
% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;
instrCounterClass =
    fn(r,'InstrCounterRep',
    fn(self,arr(unit,'InstrCounter'),
    fn('_',unit,
        let(super,app(app(app(setCounterClass,r),self),unit),
        as(record([get=proj(super,get),
            set = fn(i,nat,let('_',assign(proj(r,a),succ(deref(proj(r,a)))),app(proj(super,set),i))),
            inc = proj(super,inc),
            accesses = fn('_',unit,deref(proj(r,a)))
        ]),'InstrCounter')
    ))))
]).


% newInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0} in
% fix (instrCounterClass r) unit;

% ic = newInstrCounter unit;

% ic.get unit;

% ic.accesses unit;

% ic.inc unit;

% ic.get unit;

% ic.accesses unit;

/* ------------ */

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = lambda _:Unit. (r.a:=succ(!(r.a)); super.get unit),
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;

% ResetInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
% inc:Unit->Unit, accesses:Unit->Nat,
% reset:Unit->Unit};

% resetInstrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->ResetInstrCounter.
% lambda _:Unit.
% let super = instrCounterClass r self unit in
% {get = super.get,
% set = super.set,
% inc = super.inc,
% accesses = super.accesses,
% reset = lambda _:Unit. r.x:=0} 
% as ResetInstrCounter;

% BackupInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
% inc:Unit->Unit, accesses:Unit->Nat,
% backup:Unit->Unit, reset:Unit->Unit};

% BackupInstrCounterRep = {x: Ref Nat, a: Ref Nat, b: Ref Nat};

% backupInstrCounterClass =
% lambda r:BackupInstrCounterRep.
% lambda self: Unit->BackupInstrCounter.
% lambda _:Unit.
% let super = resetInstrCounterClass r self unit in
% {get = super.get,
% set = super.set,
% inc = super.inc,
% accesses = super.accesses,
% reset = lambda _:Unit. r.x:=!(r.b),
% backup = lambda _:Unit. r.b:=!(r.x)} 
% as BackupInstrCounter;

% newBackupInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0, b=ref 0} in
% fix (backupInstrCounterClass r) unit;

% ic = newBackupInstrCounter unit;

% (ic.inc unit; ic.get unit);

% (ic.backup unit; ic.get unit);

% (ic.inc unit; ic.get unit);

% (ic.reset unit; ic.get unit);

% ic.accesses unit;




/*
SetCounterMethodTable =  
{get: Ref <none:Unit, some:Unit->Nat>, 
set: Ref <none:Unit, some:Nat->Unit>, 
inc: Ref <none:Unit, some:Unit->Unit>}; 

packGet = 
lambda f:Unit->Nat. 
<some = f> as <none:Unit, some:Unit->Nat>;

unpackGet = 
lambda mt:SetCounterMethodTable.
case !(mt.get) of
<none=x> ==> error
| <some=f> ==> f;

packSet = 
lambda f:Nat->Unit. 
<some = f> as <none:Unit, some:Nat->Unit>;

unpackSet = 
lambda mt:SetCounterMethodTable.
case !(mt.set) of
<none=x> ==> error
| <some=f> ==> f;

packInc = 
lambda f:Unit->Unit. 
<some = f> as <none:Unit, some:Unit->Unit>;

unpackInc = 
lambda mt:SetCounterMethodTable.
case !(mt.inc) of
<none=x> ==> error
| <some=f> ==> f;

setCounterClass =
lambda r:CounterRep.
lambda self: SetCounterMethodTable.
(self.get := packGet (lambda _:Unit. !(r.x));
self.set := packSet (lambda i:Nat.  r.x:=i);
self.inc := packInc (lambda _:Unit. unpackSet self (succ (unpackGet self unit))));
*/

/* This diverges...

setCounterClass =
lambda R<:CounterRep.
lambda self: R->SetCounter.
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (self r).set (succ((self r).get unit))} 
    as SetCounter;

newSetCounter = 
lambda _:Unit.
let r = {x=ref 1} in
fix (setCounterClass [CounterRep]) r;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda R<:InstrCounterRep.
lambda self: R->InstrCounter.
let super = setCounterClass [R] self in
lambda r:R.
{get = (super r).get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
inc = (super r).inc,
accesses = lambda _:Unit. !(r.a)} as InstrCounter;


newInstrCounter = 
lambda _:Unit.
let r = {x=ref 1, a=ref 0} in
fix (instrCounterClass [InstrCounterRep]) r;

SET traceeval;

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;
*/

/* This is cool...

setCounterClass =
lambda M<:SetCounter.
lambda R<:CounterRep.
lambda self: Ref(R->M).
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
      as SetCounter;


newSetCounter = 
lambda _:Unit.
let m = ref (lambda r:CounterRep. error as SetCounter) in
let m' = setCounterClass [SetCounter] [CounterRep] m in
(m := m';
let r = {x=ref 1} in
m' r);

c = newSetCounter unit;

c.get unit;

c.set 3;

c.inc unit;

c.get unit;

setCounterClass =
lambda M<:SetCounter.
lambda R<:CounterRep.
lambda self: Ref(R->M).
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
      as SetCounter;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda M<:InstrCounter.
lambda R<:InstrCounterRep.
lambda self: Ref(R->M).
lambda r: R.
let super = setCounterClass [M] [R] self in
{get = (super r).get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
inc = (super r).inc,
accesses = lambda _:Unit. !(r.a)}     as InstrCounter;

newInstrCounter = 
lambda _:Unit.
let m = ref (lambda r:InstrCounterRep. error as InstrCounter) in
let m' = instrCounterClass [InstrCounter] [InstrCounterRep] m in
(m := m';
let r = {x=ref 1, a=ref 0} in
m' r);

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;
*/

/* James Reily's alternative: */

% Counter = {get:Unit->Nat, inc:Unit->Unit};
% inc3 = lambda c:Counter. (c.inc unit; c.inc unit; c.inc unit);

% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit};
% InstrCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat};

% CounterRep = {x: Ref Nat};
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};

% dummySetCounter =
% {get = lambda _:Unit. 0,
% set = lambda i:Nat.  unit,
% inc = lambda _:Unit. unit}
% as SetCounter;
% dummyInstrCounter =
% {get = lambda _:Unit. 0,
% set = lambda i:Nat.  unit,
% inc = lambda _:Unit. unit,
% accesses = lambda _:Unit. 0}
% as InstrCounter;
% setCounterClass =
% lambda r:CounterRep.
% lambda self: Source SetCounter.     
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat. r.x:=i,
% inc = lambda _:Unit. (!self).set (succ ((!self).get unit))}
% as SetCounter;
% newSetCounter =
% lambda _:Unit. let r = {x=ref 1} in
% let cAux = ref dummySetCounter in
% (cAux :=
% (setCounterClass r cAux);
% !cAux);

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Source InstrCounter.       /* NOT Ref */
% let super = setCounterClass r self in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)}
% as InstrCounter;
% newInstrCounter =
% lambda _:Unit. let r = {x=ref 1, a=ref 0} in
% let cAux = ref dummyInstrCounter in
% (cAux :=
% (instrCounterClass r cAux);
% !cAux);

% c = newInstrCounter unit;
% (inc3 c; c.get unit);
% (c.set(54); c.get unit);
% (c.accesses unit);

:- halt.
