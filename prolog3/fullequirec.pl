:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string. % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).        % 識別子:
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A|list(A)].             % リスト
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数

t ::=                                     % 型:
      bool                                % ブール値型
    | nat                                 % 自然数型
    | unit                                % Unit型
    | float                               % 浮動小数点数型
    | string                              % 文字列型
    | x                                   % 型変数
    | arr(t,t)                            % 関数の型
    | record(list(l:t))                   % レコードの型
    | variant(list(x:t))                  % バリアント型
    | rec(x,t)                            % 再帰型
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
tsubst(J,S,rec(X,T1),rec(X,T1_)) :- tsubst2(X,J,S,T1,T1_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
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
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,fix(M1), fix(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,inert(T1), inert(T1)).
subst(J,M,as(M1,T1), as(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,tag(L,M1,T1), tag(L,M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,case(M,Cases), case(M_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

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
eval1(Γ,tag(L,M1,T),tag(L,M1_,T)) :- eval1(Γ,M1,M1_).
eval1(Γ,case(tag(L,V11,_),Bs),M_) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(Γ,case(M1,Bs),case(M1_, Bs)) :- eval1(Γ,M1,M1_).
eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).
  
gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T)).
compute(Γ,rec(X,S1),T) :- tsubst(X,rec(X,S1),S1,T).
compute(Γ,X,T) :- x(X),gettabb(Γ,X,T).

simplify(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify(Γ,T,T).

teq(Γ,S,T) :- teq([],Γ,S,T).
teq(Seen,Γ,S,T) :- member((S,T),Seen).
teq(Seen,Γ,bool,bool).
teq(Seen,Γ,nat,nat).
teq(Seen,Γ,unit,unit).
teq(Seen,Γ,float,float).
teq(Seen,Γ,string,string).
teq(Seen,Γ,rec(X,S1),T) :- S=rec(X,S1),tsubst(X,S,S1,S1_),teq([(S,T)|Seen],Γ,S1_,T).
teq(Seen,Γ,S,rec(X,T1)) :- T=rec(X,T1),tsubst(X,T,T1,T1_),teq([(S,T)|Seen],Γ,S,T1_).
teq(Seen,Γ,X,X) :- x(X).
teq(Seen,Γ,X,T) :- x(X),gettabb(Γ,X,S),teq(Seen,Γ,S,T).
teq(Seen,Γ,S,X) :- x(X),gettabb(Γ,X,T),teq(Seen,Γ,S,T).
teq(Seen,Γ,arr(S1,S2),arr(T1,T2)) :- teq(Seen,Γ,S1,T1),teq(Seen,Γ,S2,T2).
teq(Seen,Γ,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Seen,Γ,S,T)), Tf).
teq(Seen,Γ,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Seen,Γ,S,T),Sf,Tf).

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
typeof(Γ,tag(Li, Mi, T), T) :- simplify(Γ,T,variant(Tf)),member(Li:Te,Tf),typeof(Γ,Mi, T_),teq(Γ,T_,Te).
typeof(Γ,case(M, Cases), T1) :-
    typeof(Γ,M,T),simplify(Γ,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases,[T1|RestT]),
    maplist([Tt]>>teq(Γ,Tt,T1), RestT).
typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show(Γ,X,bName) :- format('~w\n',[X]).
show(Γ,X,bVar(T)) :- format('~w : ~w\n',[X,T]).
show(Γ,X,bTVar) :- format('~w\n',[X]).
show(Γ,X,bMAbb(M,T)) :- format('~w : ~w\n',[X,T]).
show(Γ,X,bTAbb(T)) :- format('~w :: *\n',[X]).

run(X : T,Γ,[X-bVar(T)|Γ])      :- show(Γ,X,bVar(T)),!.
run(type(T),Γ,[X-bTVar(T)|Γ])   :- show(Γ,X,bTVar(T)),!.
run(type(X)=T,Γ,[X-bTAbb(T)|Γ]) :- show(Γ,X,bTAbb(T)),!.
run(X:T=M,Γ,[X-bMAbb(M_,T)|Γ])  :- typeof(Γ,M,T_),teq(Γ,T_,T),eval(Γ,M,M_),show(Γ,X,bMAbb(M_,T)),!.
run(X=M,Γ,[X-bMAbb(M_,T)|Γ])    :- typeof(Γ,M,T),eval(Γ,M,M_),show(Γ,X,bMAbb(M_,T)),!.
run(M,Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% "hello";
:- run(["hello"]).
% lambda x:A. x;
:- run([fn(x,'A',x)]).
% timesfloat 2.0 3.14159;
:- run([timesfloat(2.0,3.14159)]).
% lambda x:Bool. x;
:- run([fn(x,bool,x)]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x, false, true))) ]). 
% lambda x:Nat. succ x;
:- run([fn(x,nat, succ(x))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([app(fn(x,nat, succ(succ(x))),succ(zero) ) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T')=arr(nat,nat),
        fn(f,'T',fn(x,nat,app(f,app(f,x))))]).
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([fn(f,rec('X',arr('A','A')),fn(x,'A',app(f,x)))]).
% {x=true, y=false};
:- run([record([x=true,y=false]) ]).
% {x=true, y=false}.x;
:- run([proj(record([x=true,y=false]),x) ]).
% {true, false};
:- run([record([1=true,2=false]) ]).
% {true, false}.1;
:- run([proj(record([1=true,2=false]),1) ]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([fn(x,variant([a:bool,b:bool]),x)]).

% Counter = Rec P. {get:Nat, inc:Unit->P};
% p = 
%   let create = 
%     fix 
%       (lambda cr: {x:Nat}->Counter.
%         lambda s: {x:Nat}.
%           {get = s.x,
%           inc = lambda _:Unit. cr {x=succ(s.x)}})
%   in
%     create {x=0};
% p1 = p.inc unit;
% p1.get;
% get = lambda p:Counter. p.get;
% inc = lambda p:Counter. p.inc;
:- run([
  type('Counter') = rec('P',record([get:nat,inc:arr(unit,'P')])),
  p=let(create,
    fix(
      fn(cr,arr(record([x:nat]),'Counter'),
        fn(s,record([x:nat]),
          record([get=proj(s,x),
            inc=fn('_',unit, app(cr,record([x=succ(proj(s,x))])))
          ])
        )
      )
    ),
    app(create,record([x=zero]))),
  proj(p,get),
  p=app(proj(p,inc),unit ),
  proj(p,get),
  p=app(proj(p,inc),unit ),
  proj(p,get),
  get=fn(p,'Counter',proj(p,get)),
  inc=fn(p,'Counter',proj(p,inc)),
  app(get,p),
  p=app(app(inc,p),unit),
  app(get,p)
]).

% Hungry = Rec A. Nat -> A;
% f0 =
% fix 
%   (lambda f: Nat->Hungry.
%    lambda n:Nat.
%      f);
% f1 = f0 0;
% f2 = f1 2;

% T = Nat;
%   
% fix_T = 
% lambda f:T->T.
%   (lambda x:(Rec A.A->T). f (x x))
%   (lambda x:(Rec A.A->T). f (x x));

% D = Rec X. X->X;
% fix_D = 
% lambda f:D->D.
%   (lambda x:(Rec A.A->D). f (x x))
%   (lambda x:(Rec A.A->D). f (x x));
% diverge_D = lambda _:Unit. fix_D (lambda x:D. x);
% lam = lambda f:D->D. f;
% ap = lambda f:D. lambda a:D. f a;
% myfix = lam (lambda f:D.
%              ap (lam (lambda x:D. ap f (ap x x))) 
%                 (lam (lambda x:D. ap f (ap x x))));


% let x=true in x;
:- run([let(x,true,x)]).
% unit;
:- run([unit]).

% NatList = Rec X. <nil:Unit, cons:{Nat,X}>; 
% nil = <nil=unit> as NatList;
% cons = lambda n:Nat. lambda l:NatList. <cons={n,l}> as NatList;
% isnil = lambda l:NatList. 
% case l of
% <nil=u> ==> true
% | <cons=p> ==> false;
% hd = lambda l:NatList. 
%  case l of
%   <nil=u> ==> 0
%  | <cons=p> ==> p.1;
% tl = lambda l:NatList. 
%   case l of
%   <nil=u> ==> l
%   | <cons=p> ==> p.2;
% plus = fix (lambda p:Nat->Nat->Nat. 
%  lambda m:Nat. lambda n:Nat. 
%  if iszero m then n else succ (p (pred m) n));
% sumlist = fix (lambda s:NatList->Nat. lambda l:NatList.
%  if isnil l then 0 else plus (hd l) (s (tl l)));
% mylist = cons 2 (cons 3 (cons 5 nil));
% sumlist mylist;

:- halt.
