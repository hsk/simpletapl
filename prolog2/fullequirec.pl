:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,var(J),S).
tsubst(J,S,var(X),var(X)).
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
subst(J,M,float(F1),float(F1)).
subst(J,M,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,string(X),string(X)).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
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

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(unit).
v(float(_)).
v(string(_)).
v(fn(_,_,_)).
v(record(Mf)) :- maplist([L=M]>>v(M),Mf).
v(tag(_,M1,_)) :- v(M1).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,if(true,M2,_),M2).
eval1(G,if(false,_,M3),M3).
eval1(G,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,succ(M1),succ(M1_)) :- eval1(G,M1,M1_).
eval1(G,pred(zero),zero).
eval1(G,pred(succ(N1)),N1) :- n(N1).
eval1(G,pred(M1),pred(M1_)) :- eval1(G,M1,M1_).
eval1(G,iszero(zero),true).
eval1(G,iszero(succ(N1)),false) :- n(N1).
eval1(G,iszero(M1),iszero(M1_)) :- eval1(G,M1,M1_).
eval1(G,timesfloat(float(F1),float(F2)),float(F3)) :- F3 is F1 * F2.
eval1(G,timesfloat(V1,M2),timesfloat(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,timesfloat(M1,M2),timesfloat(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,var(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,app(fn(X,_,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,let(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,let(X,M1,M2),let(X,M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,fix(fn(X,T,M12)),M12_) :- subst(X,fix(fn(X,T,M12)),M12,M12_).
eval1(G,fix(M1),fix(M1_)) :- eval1(G,M1,M1_).
eval1(G,as(V1,_), V1) :- v(V1).
eval1(G,as(M1,T), as(M1_,T)) :- eval1(G,M1,M1_).
eval1(G,record(Mf),record(Mf_)) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,proj(record(Mf),L),M) :- member(L=M,Mf).
eval1(G,proj(M1,L),proj(M1_, L)) :- eval1(G,M1,M1_).
eval1(G,tag(L,M1,T),tag(L,M1_,T)) :- eval1(G,M1,M1_).
eval1(G,case(tag(L,V11,_),Bs),M_) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(G,case(M1,Bs),case(M1_, Bs)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).
  
gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,rec(X,S1),T) :- tsubst(X,rec(X,S1),S1,T).
compute(G,var(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- teq([],G,S,T).
teq(Seen,G,S,T) :- member((S,T),Seen).
teq(Seen,G,bool,bool).
teq(Seen,G,nat,nat).
teq(Seen,G,unit,unit).
teq(Seen,G,float,float).
teq(Seen,G,string,string).
teq(Seen,G,rec(X,S1),T) :- S=rec(X,S1),tsubst(X,S,S1,S1_),teq([(S,T)|Seen],G,S1_,T).
teq(Seen,G,S,rec(X,T1)) :- T=rec(X,T1),tsubst(X,T,T1,T1_),teq([(S,T)|Seen],G,S,T1_).
teq(Seen,G,var(X),var(X)).
teq(Seen,G,var(X),T) :- gettabb(G,X,S),teq(Seen,G,S,T).
teq(Seen,G,S,var(X)) :- gettabb(G,X,T),teq(Seen,G,S,T).
teq(Seen,G,arr(S1,S2),arr(T1,T2)) :- teq(Seen,G,S1,T1),teq(Seen,G,S2,T2).
teq(Seen,G,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Seen,G,S,T)), Tf).
teq(Seen,G,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Seen,G,S,T),Sf,Tf).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,zero,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat),!.
typeof(G,pred(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat),!.
typeof(G,iszero(M1),bool) :- typeof(G,M1,T1),teq(G,T1,nat),!.
typeof(G,unit,unit).
typeof(G,float(_),float).
typeof(G,timesfloat(M1,M2),float) :- typeof(G,M1,T1),teq(G,T1,float),typeof(G,M2,T2),teq(G,T2,float).
typeof(G,string(_),string).
typeof(G,var(X),T) :- gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,let(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,fix(M1),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),teq(G,T12,T11).
typeof(G,inert(T),T).
typeof(G,as(M1,T),T) :- typeof(G,M1,T1),teq(G,T1,T).
typeof(G,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,proj(M1,L),T) :- typeof(G,M1,T1),simplify(G,T1,record(Tf)),member(L:T,Tf).
typeof(G,tag(Li, Mi, T), T) :- simplify(G,T,variant(Tf)),member(Li:Te,Tf),typeof(G,Mi, T_),teq(G,T_,Te).
typeof(G,case(M, Cases), T1) :-
    typeof(G,M,T),simplify(G,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases,[T1|RestT]),
    maplist([Tt]>>teq(G,Tt,T1), RestT).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),G,G) :- !,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% "hello";
:- run([eval(string(hello))]).
% lambda x:A. x;
:- run([eval(fn(x,var('A'),var(x)))]).
% timesfloat 2.0 3.14159;
:- run([eval(timesfloat(float(2.0),float(3.14159))) ]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,var(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(var(x), false), true, false)),
                  fn(x,bool, if(var(x), false, true)))) ]). 
% lambda x:Nat. succ x;
:- run([eval(fn(x,nat, succ(var(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(app(fn(x,nat, succ(succ(var(x)))),succ(zero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([bind('T',bTAbb(arr(nat,nat))),
        eval(fn(f,var('T'),fn(x,nat,app(var(f),app(var(f),var(x))))))]).
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([eval(fn(f,rec('X',arr(var('A'),var('A'))),fn(x,var('A'),app(var(f),var(x)))))]).
% {x=true, y=false};
:- run([eval(record([x=true,y=false])) ]).
% {x=true, y=false}.x;
:- run([eval(proj(record([x=true,y=false]),x)) ]).
% {true, false};
:- run([eval(record([1=true,2=false])) ]).
% {true, false}.1;
:- run([eval(proj(record([1=true,2=false]),1)) ]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([eval(fn(x,variant([a:bool,b:bool]),var(x)))]).

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
  bind('Counter',bTAbb(rec('P',record([get:nat,inc:arr(unit,var('P'))])))),
  bind(p,bMAbb(let(create,
    fix(
      fn(cr,arr(record([x:nat]),var('Counter')),
        fn(s,record([x:nat]),
          record([get=proj(var(s),x),
            inc=fn('_',unit, app(var(cr),record([x=succ(proj(var(s),x))])))
          ])
        )
      )
    ),
    app(var(create),record([x=zero]))),none )),
  eval(proj(var(p),get)),
  bind(p,bMAbb(app(proj(var(p),inc),unit ),none )),
  eval(proj(var(p),get)),
  bind(p,bMAbb(app(proj(var(p),inc),unit ),none )),
  eval(proj(var(p),get)),
  bind(get,bMAbb(fn(p,var('Counter'),proj(var(p),get)),none)),
  bind(inc,bMAbb(fn(p,var('Counter'),proj(var(p),inc)),none)),
  eval(app(var(get),var(p))),
  bind(p,bMAbb(app(app(var(inc),var(p)),unit),none)),
  eval(app(var(get),var(p)))
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
:- run([eval(let(x,true,var(x)))]).
% unit;
:- run([eval(unit)]).

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
