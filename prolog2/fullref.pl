:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,unit,unit).
tsubst(J,S,float,float).
tsubst(J,S,string,string).
tsubst(J,S,top,top).
tsubst(J,S,bot,bot).
tsubst(J,S,var(J),S).
tsubst(J,S,var(X),var(X)).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,record(Mf),record(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,variant(Mf),variant(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,ref(T1),ref(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,source(T1),source(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,sink(T1),sink(T1_)) :- tsubst(J,S,T1,T1_).
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
subst(J,M,float(F1),float(F1)).
subst(J,M,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,string(X),string(X)).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
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
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
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
v(loc(_)).

extendstore(St,V1,Len,St_) :- length(St,Len),append(St,[V1],St_).
lookuploc(St,L,R) :- nth0(L,St,R).
updatestore([_|St],0,V1,[V1|St]).
updatestore([V|St],N1,V1,[V|St_]) :- N is N1 - 1, updatestore(St,N,V1,St_).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

eval1(G,St,if(true,M2,M3),M2,St).
eval1(G,St,if(false,M2,M3),M3,St).
eval1(G,St,if(M1,M2,M3),if(M1_,M2,M3),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,succ(M1),succ(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,pred(zero),zero,St).
eval1(G,St,pred(succ(NV1)),NV1,St) :- n(NV1).
eval1(G,St,pred(M1),pred(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,iszero(zero),true,St).
eval1(G,St,iszero(succ(NV1)),false,St) :- n(NV1).
eval1(G,St,iszero(M1),iszero(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,timesfloat(float(F1),float(F2)),float(F_),St) :- F_ is F1 * F2.
eval1(G,St,timesfloat(float(F1),M2),timesfloat(float(F1),M2_),St_) :- eval1(G,St,M2,M2_).
eval1(G,St,timesfloat(M1,M2),timesfloat(M1_,M2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,var(X),M,St) :- getb(G,X,bMAbb(M,_)).
eval1(G,St,app(fn(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(G,St,app(V1,M2),app(V1, M2_),St_) :- v(V1), eval1(G,St,M2,M2_,St_).
eval1(G,St,app(M1,M2),app(M1_, M2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,let(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,St,let(X,M1,M2),let(X,M1_,M2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,fix(fn(X,T11,M12)),M,St) :- subst(X,fix(fn(X,T11,M12)),M12,M).
eval1(G,St,fix(M1),fix(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,as(V1,_), V1,St) :- v(V1).
eval1(G,St,as(M1,T), as(M1_,T),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,record(Mf),record(Mf_),St_) :- e(Mf,M,Mf_,M_),eval1(G,St,M,M_,St_).
eval1(G,St,proj(record(Mf),L),M,St) :- member(L=M,Mf).
eval1(G,St,proj(M1,L),proj(M1_, L),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,tag(L,M1,T),tag(L,M1_,T),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,case(tag(L,V11,_),Bs),M_,St) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(G,St,case(M1,Bs),case(M1_, Bs),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(G,St,ref(M1),ref(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(G,St,deref(M1),deref(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(G,St,assign(V1,M2),assign(V1, M2_),St_) :- v(V1), eval1(G,St,M2,M2_,St_).
eval1(G,St,assign(M1,M2),assign(M1_, M2),St_) :- eval1(G,St,M1,M1_,St_).
eval(G,St,M,M_,St_) :- eval1(G,St,M,M1,St1),eval(G,St1,M1,M_,St_).
eval(G,St,M,M,St).

evalbinding(G,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(G,St,M,M_,St_).
evalbinding(G,St,Bind,Bind,St).

% ------------------------   SUBTYPING  ------------------------

gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,var(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,bool,bool).
teq2(G,nat,nat).
teq2(G,unit,unit).
teq2(G,float,float).
teq2(G,string,string).
teq2(G,top,top).
teq2(G,bot,bot).
teq2(G,var(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,var(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,var(X),var(X)).
teq2(G,arr(S1,S2),arr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(G,S,T)), Tf).
teq2(G,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(G,S,T),Sf,Tf).
teq2(ref(S),ref(T)) :- teq(G,S,T).
teq2(source(S),source(T)) :- teq(G,S,T).
teq2(sink(S),sink(T)) :- teq(G,S,T).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S_,T_).
subtype2(G,_,top).
subtype2(G,bot,_).
subtype2(G,arr(S1,S2),arr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype2(G,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).
subtype2(G,variant(SF),variant(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(G,S,T)),SF).
subtype2(G,ref(S),ref(T)) :- subtype(G,S,T),subtype(G,T,S).
subtype2(G,ref(S),source(T)) :- subtype(G,S,T).
subtype2(G,source(S),source(T)) :- subtype(G,S,T).
subtype2(G,ref(S),sink(T)) :- subtype(G,T,S).
subtype2(G,sink(S),sink(T)) :- subtype(G,T,S).

join(G,S,T,T) :- subtype(G,S,T).
join(G,S,T,S) :- subtype(G,T,S).
join(G,S,T,R) :- simplify(G,S,S_),simplify(G,T,T_),join2(G,S_,T_,R).
join2(G,record(SF),record(TF),record(UF_)) :-
    include([L:_]>>member(L:_,TF),SF,UF),
    maplist([L:S,L:T_]>>(member(L:T,TF),join(G,S,T,T_)),UF,UF_).
join2(G,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- meet(G,S1,T1,S_),join(G,S2,T2,T_).
join2(G,ref(S),ref(T),ref(S)) :- subtype(G,S,T),subtype(G,T,S).
join2(G,ref(S),ref(T),source(T_)) :- /* Warning: this is incomplete... */ join(G,S,T,T_).

join2(G,source(S),source(T),source(T_)) :- join(G,S,T,T_).
join2(G,ref(S),source(T),source(T_)) :- join(G,S,T,T_).
join2(G,source(S),ref(T),source(T_)) :- join(G,S,T,T_).
join2(G,sink(S),sink(T),sink(T_)) :- meet(G,S,T,T_).
join2(G,ref(S),sink(T),sink(T_)) :- meet(G,S,T,T_).
join2(G,sink(S),ref(T),sink(T_)) :- meet(G,S,T,T_).
join2(G,_,_,top).

meet(G,S,T,S) :- subtype(G,S,T).
meet(G,S,T,T) :- subtype(G,T,S).
meet(G,S,T,R) :- simplify(G,S,S_),simplify(G,T,T_),meet2(G,S_,T_,R).
meet2(G,record(SF),record(TF),record(UF_)) :-
    maplist([L:S,L:T_]>>(member(L:T,TF),meet(G,S,T,T_);T_=S),SF,SF_),
    include([L:_]>>(\+member(L:_,SF)),TF,TF_),
    append(SF_,TF_,UF_).
meet2(G,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- join(G,S1,T1,S_),meet(G,S2,T2,T_).
meet2(G,ref(S),ref(T),ref(T)) :- subtype(G,S,T), subtype(G,T,S).
meet2(G,ref(S),ref(T),source(T_)) :- meet(G,S,T,T_).
meet2(G,source(S),source(T),source(T_)) :- meet(G,S,T,T_).
meet2(G,ref(S),source(T),source(T_)) :- meet(G,S,T,T_).
meet2(G,source(S),ref(T),source(T_)) :- meet(G,S,T,T_).
meet2(G,sink(S),sink(T),sink(T_)) :- join(G,S,T,T_).
meet2(G,ref(S),sink(T),sink(T_)) :- join(G,S,T,T_).
meet2(G,sink(S),ref(T),sink(T_)) :- join(G,S,T,T_).
meet2(_,_,bot).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T) :- typeof(G,M1,T1),subtype(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3),join(G,T2,T3,T).
typeof(G,zero,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,T1),subtype(G,T1,nat).
typeof(G,pred(M1),nat) :- typeof(G,M1,T1),subtype(G,T1,nat).
typeof(G,iszero(M1),bool) :- typeof(G,M1,T1),subtype(G,T1,nat).
typeof(G,unit,unit).
typeof(G,float(_),float).
typeof(G,timesfloat(M1,M2),float) :- typeof(G,M1,T1),subtype(G,T1,float),typeof(G,M2,T2),subtype(G,T2,float).
typeof(G,string(_),string).
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,app(M1,M2),bot) :- typeof(G,M1,T1),typeof(G,M2,T2),simplify(G,T1,bot).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,let(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,fix(M1),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),subtype(G,T12,T11).
typeof(G,fix(M1),bot) :- typeof(G,M1,T1),simplify(G,T1,bot).
typeof(G,inert(T),T).
typeof(G,as(M1,T),T) :- typeof(G,M1,T1),subtype(G,T1,T).
typeof(G,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,proj(M1,L),T) :- typeof(G,M1,T1),simplify(G,T1,record(Tf)),member(L:T,Tf).
typeof(G,proj(M1,L),bot) :- typeof(G,M1,T1),simplify(G,T1,bot).
typeof(G,tag(Li, Mi, T), T) :- simplify(G,T,variant(Tf)),member(Li:Te,Tf),typeof(G,Mi, T_),subtype(G,T_,Te).
typeof(G,case(M, Cases), bot) :- typeof(G,M,T),simplify(G,T,bot),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi)]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases).
typeof(G,case(M, Cases), T_) :-
    typeof(G,M,T),simplify(G,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases,CaseTypes),
    foldl(join(G),bot,CaseTypes,T_).

typeof(G,ref(M1),ref(T1)) :- typeof(G,M1,T1).
typeof(G,deref(M1),T1) :- typeof(G,M1,T), simplify(G,T,ref(T1)).
typeof(G,deref(M1),bot) :- typeof(G,M1,T), simplify(G,T,bot).
typeof(G,deref(M1),T1) :- typeof(G,M1,T), simplify(G,T,source(T1)).
typeof(G,assign(M1,M2),unit) :- typeof(G,M1,T), simplify(G,T,ref(T1)),typeof(G,M2,T2),subtype(G,T2,T1).
typeof(G,assign(M1,M2),bot) :- typeof(G,M1,T), simplify(G,T,bot),typeof(G,M2,_).
typeof(G,assign(M1,M2),unit) :- typeof(G,M1,T), simplify(G,T,sink(T1)),typeof(G,M2,T2),subtyping(G,T2,T1).

typeof(G,loc(l),_) :- !,fail.
%typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.
% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),(G,St),(G,St_)) :- !,typeof(G,M,T),!,eval(G,St,M,M_,St_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),(G,St),([X-Bind|G],St_)) :-
  typeof(G,M,T),evalbinding(G,St,bMAbb(M,some(T)),Bind,St_),write(X),show_bind(G,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),(G,St),([X-Bind|G],St_)) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,St,bMAbb(M,some(T)),Bind,St_),show_bind(G,Bind,S),write(X),writeln(S).
run(bind(X,Bind),(G,St),([X-Bind_|G],St_)) :-
  evalbinding(G,St,Bind,Bind_,St_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,([],[]),_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([eval(fn(x,bot,var(x)))]).
% lambda x:Bot. x x;
:- run([eval(fn(x,bot,app(var(x),var(x))))]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([eval(fn(x,variant([a:bool,b:bool]),var(x)))]).
% lambda x:Top. x;
:- run([eval(fn(x,top,var(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,var(x)),fn(x,top,var(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(r,arr(top,top),app(var(r),var(r))),
                  fn(z,top,var(z)))) ]).
% (lambda r:{x:Top->Top}. r.x r.x)
%   {x=lambda z:Top.z, y=lambda z:Top.z};
:- run([eval(app(fn(r,record([x:arr(top,top)]),app(proj(var(r),x),proj(var(r),x))),
                  record([x=fn(z,top,var(z)),y=fn(z,top,var(z))])))]).
% "hello";
:- run([eval(string(hello))]).
% unit;
:- run([eval(unit)]).
% lambda x:A. x;
:- run([eval(fn(x,var('A'),var(x)))]).
% let x=true in x;
:- run([eval(let(x,true,var(x)))]).
% {x=true, y=false};
:- run([eval(record([x=true,y=false])) ]).
% {x=true, y=false}.x;
:- run([eval(proj(record([x=true,y=false]),x)) ]).
% {true, false};
:- run([eval(record([1=true,2=false])) ]).
% {true, false}.1;
:- run([eval(proj(record([1=true,2=false]),1)) ]).
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([eval(if(true,record([x=true,y=false,a=false]),record([y=false,x=record([]),b=false])))]).
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
% let a = ref 1 in !a;
:- run([eval(let(a,ref(succ(zero)),deref(var(a))))]).
% let a = ref 2 in (a := (succ (!a)); !a);
:- run([eval(let(a,ref(succ(succ(zero))),let('_',assign(var(a),succ(deref(var(a)))),deref(var(a))))) ]).

:- halt.
