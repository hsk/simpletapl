:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= top | bot.                         % キーワード:
syntax(x). x(X) :- \+w(X),atom(X).       % 識別子:
syntax(l). l(L) :- atom(L) ; integer(L). % ラベル
list(A) ::= [] | [A|list(A)].            % リスト

t ::=                                    % 型:
      top                                % 最大の型
    | bot                                % 最小の型
    | arr(t,t)                           % 関数の型
    | record(list(l:t))                  % レコードの型
    .
m ::=                                    % 項:
      x                                  % 変数
    | fn(x,t,m)                          % ラムダ抽象
    | app(m,m)                           % 関数適用
    | record(list(l=m))                  % レコード
    | proj(m,l)                          % 射影
    .
v ::=                                    % 値:
      fn(x,t,m)                          % ラムダ抽象
    | record(list(l=v))                  % レコード
    .

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(X,M,A,B):-writeln(error:subst(X,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,record(Mf),record(Mf_)) :- e(Mf,M,Mf_,M_),eval1(Γ,M,M_).
eval1(Γ,proj(record(Mf),L),M) :- member(L=M,Mf).
eval1(Γ,proj(M1,L),proj(M1_, L)) :- eval1(Γ,M1,M1_).

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(Γ,T1,T2) :- T1=T2.
subtype(Γ,_,top).
subtype(Γ,bot,_).
subtype(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype(Γ,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(Γ,S,T)),TF).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,X,T) :- x(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_),!.
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,app(M1,M2),bot) :- typeof(Γ,M1,bot),typeof(Γ,M2,T2).
typeof(Γ,record(Mf),record(Tf)) :- maplist([L=M,L:T]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),bot) :- typeof(Γ,M1,bot).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,record(Tf)), member(L:T,Tf).
typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show(Γ,X,bName) :- format('~w\n',[X]).
show(Γ,X,bVar(T)) :- format('~w : ~w\n',[X,T]).

run(X : T,Γ,[X-bVar(T)|Γ]) :- x(X),t(T),show(Γ,X,bVar(T)).
run(M,Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T),!.
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

%lambda x:Top. x;
:- run([fn(x,top,x)]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([app(fn(x,top,x),fn(x,top,x))]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([app(fn(x,arr(top,top),x),fn(x,top,x))]).

%(lambda r:{x:Top->Top}. r.x r.x) 
:- run([fn(r,record([x:arr(top,top)]), app(proj(r,x),proj(r,x)))]).

%{x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([record([x=fn(z,top,z),y=fn(z,top,z)])]).

%lambda x:Bot. x;
:- run([fn(x,bot,x)]).
%lambda x:Bot. x x; 
:- run([fn(x,bot,app(x,x))]).

:- run([
  % x : Top;
  x : top,
  % y : Bot;
  y : bot,
  % {x,y};
  record([1=x,2=y])
]).

:- halt.
