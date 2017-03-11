:- op(920, xfx, [<:]).
:- op(600, xfy, [::]).
:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | top | true | false | zero. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).        % 識別子:
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A|list(A)].             % リスト

k ::=                                     % カインド:
      *                                   % 真の型のカインド
    | kArr(k,k)                           % 演算子のカインド
    .
ι ::= invariant                           % 非変な(更新可能)フィールド
    | covariant                           % 共変な(更新不能)フィールド
    .
t ::=                                     % 型:
      bool                                % ブール値型
    | nat                                 % 自然数型
    | unit                                % Unit型
    | float                               % 浮動小数点数型
    | string                              % 文字列型
    | top                                 % 最大の型
    | x                                   % 型変数
    | arr(t,t)                            % 関数の型
    | record(list(l:(ι,t)))               % レコードの型
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
    | record(list(l=(ι,m)))               % レコード
    | update(m,l,m)                       % フィールド更新
    | proj(m,l)                           % 射影
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
    | record(list(l=(ι,v)))               % レコード
    | pack(t,v,t)                         % パッケージ化
    | tfn(x,t,v)                          % 型抽象
    .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,top,top).
tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,record(Mf),record(Mf_)) :- maplist([L:(Vari,T),L:(Vari,T_)]>>tsubst(J,S,T,T_),Mf,Mf_).
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
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=(Vari,Mi),L=(Vari,Mi_)]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,tfn(TX,T,M2),tfn(TX,T,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,pack(T1,M2,T3),pack(T1,M2_,T3)) :- subst(J,M,M2,M2_).
subst(J,M,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- subst2(X,J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,update(M1,L,M2),update(M1_,L,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
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
tmsubst(J,M,record(Mf),record(Mf_)) :- maplist([L=(Vari,Mi),L=(Vari,Mi_)]>>tmsubst(J,M,Mi,Mi_),Mf,Mf_).
tmsubst(J,M,proj(M1,L),proj(M1_,L)) :- tmsubst(J,M,M1,M1_).
tmsubst(J,S,tfn(TX,T1,M2),tfn(TX,T1_,M2_)) :- tsubst2(TX,J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst(J,S,pack(T1,M2,T3),pack(T1_,M2_,T3_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_),tsubst(J,S,T3,T3_).
tmsubst(J,S,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,update(M1,L,M2),update(M1_,L,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

maketop(*, top).
maketop(kArr(K1,K2),abs('_',K1,K2_)) :- maketop(K2,K2_).

% ------------------------   EVALUATION  ------------------------

e([L=(Vari,M)|Mf],M,[L=(Vari,M_)|Mf],M_) :- \+v(M).
e([L=(Vari,M)|Mf],M1,[L=(Vari,M)|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

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
eval1(Γ,proj(record(Mf),L),M) :- v(record(Mf)),member(L=(_,M),Mf).
eval1(Γ,proj(M1,L),proj(M1_, L)) :- eval1(Γ,M1,M1_).
eval1(Γ,pack(T1,M2,T3),pack(T1,M2_, T3)) :- eval1(Γ,M2,M2_).
eval1(Γ,unpack(_,X,pack(T11,V12,_),M2),M) :- v(V12),subst(X,V12,M2,M2_),tmsubst(X,T11,M2_,M).
eval1(Γ,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,update(record(Mf), L, V2),record(Mf_)) :-
  v(record(Mf)),v(V2),
  maplist([ML=(Var,M),ML=(Var,R)]>>(ML=L,R=V2;R=M), Mf,Mf_).
eval1(Γ,update(V1, L, M2),update(V1, L, M2_)) :- v(V1),eval1(Γ,M2,M2_).
eval1(Γ,update(M1, L, M2),update(M1_, L, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,tapp(tfn(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,tapp(M1,T2),tapp(M1_,T2)) :- eval1(Γ,M1,M1_).
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

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
teq2(Γ,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:(TVar,T)]>>(member(L:(TVar,S),Sf),teq(Γ,S,T)), Tf).
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
kindof1(Γ,record(Tf),*) :- maplist([L:(_,S)]>>kindof(Γ,S,*),Tf).
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
subtype2(Γ,X,T) :- x(X),promote(Γ,X,S),subtype(Γ,S,T).
subtype2(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype2(Γ,record(SF),record(TF)) :- maplist([L:(Vart,T)]>>(member(L:(Vars,S),SF),(Vars=invariant;Vart=covariant),subtype(Γ,S,T)),TF).
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
    maplist([L:(SVar,S),L:(Var,T_)]>>(member(L:(TVar,T),TF),(SVar=TVar,Var=SVar;Var=invariant),join(Γ,S,T,T_)),UF,UF_).
join2(Γ,all(TX,S1,S2),all(_,T1,T2),all(TX,S1,T2_)) :-
      subtype(Γ,S1,T1),subtype(Γ,T1,S1),
      join([TX-bTVar(T1)|Γ],T1,T2,T2_).
join2(Γ,all(TX,S1,S2),all(_,T1,T2),top).
join2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- meet(Γ,S1,T1,S_),join(Γ,S2,T2,T_).
join2(Γ,_,_,top).


meet(Γ,S,T,S) :- subtype(Γ,S,T).
meet(Γ,S,T,T) :- subtype(Γ,T,S).
meet(Γ,S,T,R) :- simplify(Γ,S,S_),simplify(Γ,T,T_),meet2(Γ,S_,T_,R).
meet2(Γ,record(SF),record(TF),record(UF_)) :-
    maplist([L:(SVar,S),L:(Var,T_)]>>(member(L:(TVar,T),TF),(SVar=TVar,Var=SVar;Var=covariant),meet(Γ,S,T,T_);T_=S),SF,SF_),
    include([L:_]>>(\+member(L:_,SF)),TF,TF_),
    append(SF_,TF_,UF_).
meet2(Γ,all(TX,S1,S2),all(_,T1,T2),all(TX,S1,T2_)) :-
    subtype(Γ,S1,T1),subtype(Γ,T1,S1),
    meet([TX-bTVar(T1)|Γ],T1,T2,T2_).
meet2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- join(Γ,S1,T1,S_),meet(Γ,S2,T2,T_).

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
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),subtype(Γ,T12,T11).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- kindof(Γ,T,*),typeof(Γ,M1,T1),subtype(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([L=(Var,M),L:(Var,T)]>>typeof(Γ,M,T),Mf,Tf),!.
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),lcst(Γ,T1,record(Tf)),member(L:(_,T),Tf).
typeof(Γ,update(M1, L, M2),T1) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),lcst(Γ,T1,record(Tf)),member(L:(invariant,T),Tf),subtype(Γ,T2,T).
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

check_someBind(TBody,pack(_,T12,_),bMAbb(T12,some(TBody))).
check_someBind(TBody,_,bVar(TBody)).

run(X<:T,Γ,[X-bTVar(T)|Γ]) :- x(X),t(T),kindof(Γ,T,_),write(X),show(Γ,X,bTVar(T),R),writeln(R).
run(type(X)=T,Γ,[X-bTAbb(T,K)|Γ]) :- x(X),t(T),kindof(Γ,T,K), show(Γ,X,bTAbb(T,K)).
run(X:T,Γ,[X-bVar(T)|Γ]) :- x(X),t(T),show(Γ,X,bVar(T)).
run(X=M,Γ,[X-bMAbb(M_,T)|Γ]) :- x(X),m(M),typeof(Γ,M,T), eval(Γ,M,M_), show(Γ,X,bMAbb(M_,T)).
run(X:T=M,Γ,[X-bMAbb(M_,T)|Γ]) :- x(X),t(T),m(M),typeof(Γ,M,T1), subtype(Γ,T1,T), eval(Γ,M,M_), show(Γ,X,bMAbb(M_,T)).
run({TX,X}=M,Γ,[X-B,TX-bTVar(TBound)|Γ]) :-
    x(TX),x(X),m(M),
    !,typeof(Γ,M,T),
    lcst(Γ,T,some(_,TBound,TBody)),
    eval(Γ,M,M_),
    check_someBind(TBody,M_,B),
    writeln(TX),write(X),write(' : '),writeln(TBody).

run(M,Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Top. x;
:- run([(fn(x,top,x))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([(app(fn(x,top,x),fn(x,top,x)))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([(app(fn(x,arr(top,top),x),fn(x,top,x)))]).
% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([(app(fn(r,record([x:(covariant,arr(top,top))]),app(proj(r,x),proj(r,x))),
                  record([x=(covariant,fn(z,top,z)),y=(covariant,fn(z,top,z))])))]).
% "hello";
:- run([("hello")]).
% unit;
:- run([(unit)]).
% lambda x:A. x;
:- run([(fn(x,'A',x))]).
% let x=true in x;
:- run([(let(x,true,x))]).
% {x=true, y=false};
:- run([(record([x=(covariant,true),y=(covariant,false)])) ]).
% {x=true, y=false}.x;
:- run([(proj(record([x=(covariant,true),y=(covariant,false)]),x)) ]).
% {true, false};
:- run([(record([1=(covariant,true),2=(covariant,false)])) ]).
% {true, false}.1;
:- run([(proj(record([1=(covariant,true),2=(covariant,false)]),1)) ]).
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([(if(true,record([x=(covariant,true),y=(covariant,false),a=(covariant,false)]),
record([y=(covariant,false),x=(covariant,record([])),b=(covariant,false)])))]).
% timesfloat 2.0 3.14159;
:- run([(timesfloat(2.0,3.14159))]).
% lambda X. lambda x:X. x;
:- run([(tfn('X',top,fn(x,'X',x)))]).
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([(tapp(tfn('X',top,fn(x,'X',x)),all('X',top,arr('X','X'))) )]).
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([(tfn('X',arr(top,top),fn(x,'X',app(x,x)))) ]).
% lambda x:Bool. x;
:- run([(fn(x,bool,x))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([(app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x, false, true)))) ]).
% lambda x:Nat. succ x;
:- run([(fn(x,nat, succ(x)))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([(app(fn(x,nat, succ(succ(x))),succ(zero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T')=arr(nat,nat),
        fn(f,'T',fn(x,nat,app(f,app(f,x))))]).
% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([(pack(all('Y',top,'Y'),fn(x,all('Y',top,'Y'),x),some('X',top,arr('X','X')) ))]).


% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
:- run([(pack(nat,record([c=(covariant,zero),f=(covariant,fn(x,nat,succ(x)))]),
         some('X',top,record([c:(covariant,'X'),f:(covariant,arr('X',nat))]))))]).
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);


% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;

% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;

% f = lambda X.lambda Y.lambda f:Pair X Y. f;

% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);

% pr = pair [Nat] [Bool] 0 false;
% fst [Nat] [Bool] pr;
% snd [Nat] [Bool] pr;

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
