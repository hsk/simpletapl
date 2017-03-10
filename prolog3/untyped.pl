:- op(10,xf,[/]).
:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

x ::= atom.    % 識別子:
m ::=          % 項:
      x        % 変数
    | fn(x,m)  % ラムダ抽象
    | app(m,m) % 関数適用
    .
v ::=          % 値:
      fn(x,m)  % ラムダ抽象
    .

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X,M2),fn(X,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).

% ------------------------   EVALUATION  ------------------------

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,app(fn(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   MAIN  ------------------------

run(X/,Γ,[X-name|Γ]) :- !,writeln(X).
run(M,Γ,Γ) :- !,m(M),!,eval(Γ,M,M_),!, writeln(M_).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    %x/;
    x/,
    %x;
    x,
    %lambda x. x;
    fn(x,x),
    %(lambda x. x) (lambda x. x x); 
    app(fn(x,x),fn(x,app(x,x) )) ,
    %(lambda z. (lambda y. y) z) (lambda x. x x); 
    app(fn(z,app(fn(y,y),z)), fn(x,app(x,x) )) ,
    %(lambda x. (lambda x. x) x) (lambda x. x x); 
    app(fn(x,app(fn(x,x),x)), fn(x,app(x,x) )) ,
    %(lambda x. (lambda x. x) x) (lambda z. z z); 
    app(fn(x,app(fn(x,x),x)), fn(z,app(z,z) ))
]).

:- halt.
