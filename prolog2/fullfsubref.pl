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
tsubst(J,S,all(TX,T1,T2),all(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
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
subst(J,M,try(M1,M2), try(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,error, error).
subst(J,M,tfn(TX,T1,M2),tfn(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
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
tmsubst(J,S,float(F1),float(F1)).
tmsubst(J,S,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,string(X),string(X)).
tmsubst(J,S,var(X),var(X)).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X,M1,M2),let(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,fix(M1), fix(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,inert(T1), inert(T1)).
tmsubst(J,S,as(M1,T1),as(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>tmsubst(J,S,Mi,Mi_),Mf,Mf_).
tmsubst(J,S,proj(M1,L),proj(M1_,L)) :- tmsubst(J,S,M1,M1_).
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
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

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
v(tfn(_,_,_)).

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
eval_context(record(Mf),ME,record(MH),H) :- \+v(M1), e(Mf,ME,MH,H).
eval_context(try(M1,M2),M1,try(H,M2),H).
eval_context(M1,M1,H,H) :- \+v(M1).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

eval1(G,St,if(true,M2,M3),M2,St).
eval1(G,St,if(false,M2,M3),M3,St).
eval1(G,St,pred(zero),zero,St).
eval1(G,St,pred(succ(NV1)),NV1,St) :- n(NV1).
eval1(G,St,iszero(zero),true,St).
eval1(G,St,iszero(succ(NV1)),false,St) :- n(NV1).
eval1(G,St,timesfloat(float(F1),float(F2)),float(F_),St) :- F_ is F1 * F2.
eval1(G,St,var(X),M,St) :- getb(G,X,bMAbb(M,_)).
eval1(G,St,app(fn(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(G,St,let(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,St,fix(fn(X,T11,M12)),M,St) :- subst(X,fix(fn(X,T11,M12)),M12,M).
eval1(G,St,as(V1,_), V1,St) :- v(V1).
eval1(G,St,proj(record(Mf),L),M,St) :- member(L=M,Mf).
eval1(G,St,case(tag(L,V11,_),Bs),M_,St) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(G,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(G,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(G,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(G,St,tapp(tfn(X,M11),T2),M11_,St_) :- tmsubst(X,T2,M11,M11_).
eval1(G,St,try(error, M2), M2,St).
eval1(G,St,try(V1, M2), V1,St) :- v(V1).
eval1(G,St,try(M1, M2), try(M1_,M2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,error,_,_) :- !, fail.
eval1(G,St,M,error,St) :- eval_context(M,error,_,_),!.
eval1(G,St,M,error,St) :- eval_context(M,M,_,_),!,fail.
eval1(G,St,M,M_,St_) :- eval_context(M,ME,M_,H),eval1(G,St,ME,H,St_).

eval(G,St,M,M_,St_) :- eval1(G,St,M,M1,St1),eval(G,St1,M1,M_,St_).
eval(G,St,M,M,St).

evalbinding(G,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(G,St,M,M_,St_).
evalbinding(G,St,Bind,Bind,St).

% ------------------------   SUBTYPING  ------------------------

promote(G,var(X), T) :- getb(G,X,bTVar(T)).

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
teq2(G,ref(S),ref(T)) :- teq(G,S,T).
teq2(G,source(S),source(T)) :- teq(G,S,T).
teq2(G,sink(S),sink(T)) :- teq(G,S,T).
teq2(G,all(TX,S1,S2),all(_,T1,T2)) :- teq(G,S1,T1),teq([TX-bName|G],S2,T2).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S_,T_).
subtype2(G,_,top).
subtype2(G,bot,_).
subtype2(G,var(X),T) :- promote(G,var(X),S),subtype(G,S,T).
subtype2(G,arr(S1,S2),arr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype2(G,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).
subtype2(G,variant(SF),variant(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(G,S,T)),SF).
subtype2(G,ref(S),ref(T)) :- subtype(G,S,T),subtype(G,T,S).
subtype2(G,ref(S),source(T)) :- subtype(G,S,T).
subtype2(G,source(S),source(T)) :- subtype(G,S,T).
subtype2(G,ref(S),sink(T)) :- subtype(G,T,S).
subtype2(G,sink(S),sink(T)) :- subtype(G,T,S).
subtype2(G,all(TX,S1,S2),all(_,T1,T2)) :-
        subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).

join(G,S,T,T) :- subtype(G,S,T).
join(G,S,T,S) :- subtype(G,T,S).
join(G,S,T,R) :- simplify(G,S,S_),simplify(G,T,T_),join2(G,S_,T_,R).
join2(G,record(SF),record(TF),record(UF_)) :-
    include([L:_]>>member(L:_,TF),SF,UF),
    maplist([L:S,L:T_]>>(member(L:T,TF),join(G,S,T,T_)),UF,UF_).
join2(G,all(TX,S1,S2),all(_,T1,T2),all(TX,S1,T2_)) :-
      subtype(G,S1,T1),subtype(G,T1,S1),
      join([TX-bTVar(T1)|G],T1,T2,T2_).
join2(G,all(TX,S1,S2),all(_,T1,T2),top).
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
meet2(G,all(TX,S1,S2),all(_,T1,T2),all(TX,S1,T2_)) :-
    subtype(G,S1,T1),subtype(G,T1,S1),
    meet([TX-bTVar(T1)|G],T1,T2,T2_).
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

lcst(G,S,T) :- simplify(G,S,S_),lcst2(G,S_,T).
lcst2(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst2(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T) :- typeof(G,M1,T1),subtype(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), join(G,T2,T3,T).
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
typeof(G,app(M1,M2),bot) :- typeof(G,M1,T1),typeof(G,M2,T2),lcst(G,T1,bot).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),lcst(G,T1,arr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,let(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,fix(M1),T12) :- typeof(G,M1,T1),lcst(G,T1,arr(T11,T12)),subtype(G,T12,T11).
typeof(G,fix(M1),bot) :- typeof(G,M1,T1),lcst(G,T1,bot).
typeof(G,inert(T),T).
typeof(G,as(M1,T),T) :- typeof(G,M1,T1),subtype(G,T1,T).
typeof(G,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,proj(M1,L),T) :- typeof(G,M1,T1),lcst(G,T1,record(Tf)),member(L:T,Tf).
typeof(G,proj(M1,L),bot) :- typeof(G,M1,T1),lcst(G,T1,bot).
typeof(G,tag(Li, Mi, T), T) :- simplify(G,T,variant(Tf)),member(Li:Te,Tf),typeof(G,Mi, T_),subtype(G,T_,Te).
typeof(G,case(M, Cases), bot) :- typeof(G,M,T),lcst(G,T,bot),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi)]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases).
typeof(G,case(M, Cases), T_) :-
    typeof(G,M,T),lcst(G,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases,CaseTypes),
    foldl(join(G),bot,CaseTypes,T_).
typeof(G,ref(M1),ref(T1)) :- typeof(G,M1,T1).
typeof(G,deref(M1),T1) :- typeof(G,M1,T), lcst(G,T,ref(T1)).
typeof(G,deref(M1),bot) :- typeof(G,M1,T), lcst(G,T,bot).
typeof(G,deref(M1),T1) :- typeof(G,M1,T), lcst(G,T,source(T1)).
typeof(G,assign(M1,M2),unit) :- typeof(G,M1,T), lcst(G,T,ref(T1)),typeof(G,M2,T2),subtype(G,T2,T1).
typeof(G,assign(M1,M2),bot) :- typeof(G,M1,T), lcst(G,T,bot),typeof(G,M2,_).
typeof(G,assign(M1,M2),unit) :- typeof(G,M1,T), lcst(G,T,sink(T1)),typeof(G,M2,T2),subtyping(G,T2,T1).
typeof(G,loc(l),_) :- !,fail.
typeof(G,try(M1,M2),T) :- typeof(G,M1,T1),typeof(G,M2,T2),join(G,T1,T2,T).
typeof(G,error,bot).
typeof(G,tfn(TX,T1,M2),all(TX,T1,T2)) :- typeof([TX-bTVar(T1)|G],M2,T2),!.
typeof(G,tapp(M1,T2),T12_) :- typeof(G,M1,T1),lcst(G,T1,all(X,T11,T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
%typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' <: %w',[T]). 
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
:- run([eval(app(fn(x,arr(top,top),var(x)),fn(x,top,var(x))))]).
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
% lambda X. lambda x:X. x;
:- run([eval(tfn('X',top,fn(x,var('X'),var(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(tapp(tfn('X',top,fn(x,var('X'),var(x))),all('X',top,arr(var('X'),var('X')))) )]).
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([eval(tfn('X',arr(top,top),fn(x,var('X'),app(var(x),var(x))))) ]).

% lambda x:Bool. x;
:- run([eval(fn(x,bool,var(x)))]).
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true);
:- run([eval(app(fn(x,arr(bool,bool), if(app(var(x), false), true, false)),
                  fn(x,bool, if(var(x), false, true)))) ]).
% if error then true else false;
:- run([eval(if(error,true,false))]).

% error true;
:- run([eval(app(error,true))]).
% (lambda x:Bool. x) error;
:- run([eval(app(fn(x,bool,var(x)),error))]).
% lambda x:Nat. succ x;
:- run([eval(fn(x,nat, succ(var(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(app(fn(x,nat, succ(succ(var(x)))),succ(zero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([bind('T',bTAbb(arr(nat,nat))),
        eval(fn(f,var('T'),fn(x,nat,app(var(f),app(var(f),var(x))))))]).

/* Alternative object encodings */

% CounterRep = {x: Ref Nat};

% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}; 

% setCounterClass =
% lambda r:CounterRep.
% lambda self: Unit->SetCounter.
% lambda _:Unit.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (self unit).set (succ((self unit).get unit))} 
%     as SetCounter;

% newSetCounter = 
% lambda _:Unit.
% let r = {x=ref 1} in
% fix (setCounterClass r) unit;

% c = newSetCounter unit;
% c.get unit;

% InstrCounter = {get:Unit->Nat, 
% set:Nat->Unit, 
% inc:Unit->Unit,
% accesses:Unit->Nat};

% InstrCounterRep = {x: Ref Nat, a: Ref Nat};

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;

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

% try error with true;
:- run([eval(try(error,true))]).
% try if true then error else true with false;
:- run([eval(try(if(true,error,true),false))]).

:- halt.
