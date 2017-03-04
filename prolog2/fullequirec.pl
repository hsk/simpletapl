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

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,some(T))).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

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
eval1(Γ,timesfloat(float(F1),float(F2)),float(F3)) :- F3 is F1 * F2.
eval1(Γ,timesfloat(V1,M2),timesfloat(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,timesfloat(M1,M2),timesfloat(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,var(X),M) :- getb(Γ,X,bMAbb(M,_)).
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

evalbinding(Γ,bMAbb(M,T),bMAbb(M_,T)) :- eval(Γ,M,M_).
evalbinding(Γ,Bind,Bind).
  
gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T)).
compute(Γ,rec(X,S1),T) :- tsubst(X,rec(X,S1),S1,T).
compute(Γ,var(X),T) :- gettabb(Γ,X,T).

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
teq(Seen,Γ,var(X),var(X)).
teq(Seen,Γ,var(X),T) :- gettabb(Γ,X,S),teq(Seen,Γ,S,T).
teq(Seen,Γ,S,var(X)) :- gettabb(Γ,X,T),teq(Seen,Γ,S,T).
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
typeof(Γ,float(_),float).
typeof(Γ,timesfloat(M1,M2),float) :- typeof(Γ,M1,T1),teq(Γ,T1,float),typeof(Γ,M2,T2),teq(Γ,T2,float).
typeof(Γ,string(_),string).
typeof(Γ,var(X),T) :- gett(Γ,X,T).
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

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar,'').
show_bind(Γ,bMAbb(M,none),R) :- typeof(Γ,M,T),swritef(R,' : %w',[T]).
show_bind(Γ,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(Γ,bTAbb(T),' :: *').

run(eval(M),Γ,Γ) :- !,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),Γ,[X-Bind|Γ]) :-
  typeof(Γ,M,T),evalbinding(Γ,bMAbb(M,some(T)),Bind),write(X),show_bind(Γ,Bind,S),writeln(S),!.
run(bind(X,bMAbb(M,some(T))),Γ,[X-Bind|Γ]) :-
  typeof(Γ,M,T_),teq(Γ,T_,T),evalbinding(Γ,bMAbb(M,some(T)),Bind),show_bind(Γ,Bind,S),write(X),writeln(S),!.
run(bind(X,Bind),Γ,[X-Bind_|Γ]) :-
  evalbinding(Γ,Bind,Bind_),show_bind(Γ,Bind_,S),write(X),writeln(S),!.

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
