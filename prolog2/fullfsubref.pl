:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

l(L) :- atom(L) ; integer(L).

t(T) :- T = bool
      ; T = nat
      ; T = unit
      ; T = float
      ; T = string
      ; T = top
      ; T = bot
      ; T = var(X)           , atom(X)
      ; T = arr(T1,T2)       , t(T1),t(T2)
      ; T = record(Tf)       , maplist([X:T1]>>(l(X),t(T1)),Tf)
      ; T = variant(Tf)      , maplist([X:T1]>>(atom(X),t(T1)),Tf)
      ; T = ref(T1)          , t(T1)
      ; T = source(T1)       , t(T1)
      ; T = sink(T1)         , t(T1)
      ; T = all(X,T1,T2)     , atom(X),t(T1),t(T2)
      .
m(M) :- M = true
      ; M = false
      ; M = if(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = zero
      ; M = succ(M1)         , m(M1)
      ; M = pred(M1)         , m(M1)
      ; M = iszero(M1)       , m(M1)
      ; M = unit
      ; M = float(F)         , float(F)
      ; M = timesfloat(M1,M2), m(M1),m(M2)
      ; M = string(X)        , atom(X)
      ; M = var(X)           , atom(X)
      ; M = fn(X,T1,M1)     , atom(X),t(T1),m(M1)
      ; M = app(M1,M2)       , m(M1),m(M2)
      ; M = let(X,M1,M2)     , atom(X),m(M1),m(M2)
      ; M = fix(M1)          , m(M1)
      ; M = inert(T1)        , t(T1)
      ; M = as(M1,T1)   , m(M1),t(T1)
      ; M = record(Tf)       , maplist([X=M1]>>(l(X),m(M1)), Mf)
      ; M = proj(M1,L)       , m(M1),l(L)
      ; M = case(M1,Cases)   , m(M1), maplist([X=(X1,M2)]>>(atom(X),atom(X1),m(M2)), Cases)
      ; M = tag(X,M1,T1)     , atom(X),m(M1),t(T1)
      ; M = loc(I)           , integer(I)
      ; M = ref(M1)          , m(M1)
      ; M = deref(M1)        , m(M1) 
      ; M = assign(M1,M2)    , m(M1),m(M2)
      ; M = error
      ; M = try(M1,M2)       , m(M1),m(M2)
      ; M = tfn(TX,T1,M1)   , atom(TX),t(T1),m(M1)
      ; M = tapp(M1,T1)      , m(M1),t(T1)
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
subst(J,M,case(M1,Cases), case(M1_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M2),L=(X,M2_)]>>subst(J,M,M2,M2_), Cases,Cases_).
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
eval_context(record(Mf),ME,record(MH),H) :- \+v(record(Mf)), e(Mf,ME,MH,H).
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
eval1(Γ,St,timesfloat(float(F1),float(F2)),float(F_),St) :- F_ is F1 * F2.
eval1(Γ,St,var(X),M,St) :- getb(Γ,X,bMAbb(M,_)).
eval1(Γ,St,app(fn(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,St,let(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,St,fix(fn(X,T11,M12)),M,St) :- subst(X,fix(fn(X,T11,M12)),M12,M).
eval1(Γ,St,as(V1,_), V1,St) :- v(V1).
eval1(Γ,St,proj(record(Mf),L),M,St) :- member(L=M,Mf).
eval1(Γ,St,case(tag(L,V11,_),Bs),M_,St) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(Γ,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(Γ,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(Γ,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(Γ,St,tapp(tfn(X,M11),T2),M11_,St_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,St,try(error, M2), M2,St).
eval1(Γ,St,try(V1, M2), V1,St) :- v(V1).
eval1(Γ,St,try(M1, M2), try(M1_,M2),St_) :- eval1(Γ,St,M1,M1_,St_).
eval1(Γ,St,error,_,_) :- !, fail.
eval1(Γ,St,M,error,St) :- eval_context(M,error,_,_),!.
eval1(Γ,St,M,M_,St_) :- eval_context(M,ME,M_,H),M\=ME,eval1(Γ,St,ME,H,St_).

eval(Γ,St,M,M_,St_) :- eval1(Γ,St,M,M1,St1),eval(Γ,St1,M1,M_,St_).
eval(Γ,St,M,M,St).

evalbinding(Γ,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(Γ,St,M,M_,St_).
evalbinding(Γ,St,Bind,Bind,St).

% ------------------------   SUBTYPING  ------------------------

promote(Γ,var(X), T) :- getb(Γ,X,bTVar(T)).

gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T)).
compute(Γ,var(X),T) :- gettabb(Γ,X,T).

simplify(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify(Γ,T,T).

teq(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_),teq2(Γ,S_,T_).
teq2(Γ,bool,bool).
teq2(Γ,nat,nat).
teq2(Γ,unit,unit).
teq2(Γ,float,float).
teq2(Γ,string,string).
teq2(Γ,top,top).
teq2(Γ,bot,bot).
teq2(Γ,var(X),T) :- gettabb(Γ,X,S),teq(Γ,S,T).
teq2(Γ,S,var(X)) :- gettabb(Γ,X,T),teq(Γ,S,T).
teq2(Γ,var(X),var(X)).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).
teq2(Γ,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(Γ,S,T)), Tf).
teq2(Γ,variant(Sf),variant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(Γ,S,T),Sf,Tf).
teq2(Γ,ref(S),ref(T)) :- teq(Γ,S,T).
teq2(Γ,source(S),source(T)) :- teq(Γ,S,T).
teq2(Γ,sink(S),sink(T)) :- teq(Γ,S,T).
teq2(Γ,all(TX,S1,S2),all(_,T1,T2)) :- teq(Γ,S1,T1),teq([TX-bName|Γ],S2,T2).

subtype(Γ,S,T) :- teq(Γ,S,T).
subtype(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_), subtype2(Γ,S_,T_).
subtype2(Γ,_,top).
subtype2(Γ,bot,_).
subtype2(Γ,var(X),T) :- promote(Γ,var(X),S),subtype(Γ,S,T).
subtype2(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype2(Γ,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(Γ,S,T)),TF).
subtype2(Γ,variant(SF),variant(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(Γ,S,T)),SF).
subtype2(Γ,ref(S),ref(T)) :- subtype(Γ,S,T),subtype(Γ,T,S).
subtype2(Γ,ref(S),source(T)) :- subtype(Γ,S,T).
subtype2(Γ,source(S),source(T)) :- subtype(Γ,S,T).
subtype2(Γ,ref(S),sink(T)) :- subtype(Γ,T,S).
subtype2(Γ,sink(S),sink(T)) :- subtype(Γ,T,S).
subtype2(Γ,all(TX,S1,S2),all(_,T1,T2)) :-
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
typeof(Γ,float(_),float).
typeof(Γ,timesfloat(M1,M2),float) :- typeof(Γ,M1,T1),subtype(Γ,T1,float),typeof(Γ,M2,T2),subtype(Γ,T2,float).
typeof(Γ,string(_),string).
typeof(Γ,var(X),T) :- !,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_),!.
typeof(Γ,app(M1,M2),bot) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),lcst(Γ,T1,bot).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,fix(M1),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),subtype(Γ,T12,T11).
typeof(Γ,fix(M1),bot) :- typeof(Γ,M1,T1),lcst(Γ,T1,bot).
typeof(Γ,inert(T),T).
typeof(Γ,as(M1,T),T) :- typeof(Γ,M1,T1),subtype(Γ,T1,T).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,T1),lcst(Γ,T1,record(Tf)),member(L:T,Tf).
typeof(Γ,proj(M1,L),bot) :- typeof(Γ,M1,T1),lcst(Γ,T1,bot).
typeof(Γ,tag(Li, Mi, T), T) :- simplify(Γ,T,variant(Tf)),member(Li:Te,Tf),typeof(Γ,Mi, T_),subtype(Γ,T_,Te).
typeof(Γ,case(M, Cases), bot) :- typeof(Γ,M,T),lcst(Γ,T,bot),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi)]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases).
typeof(Γ,case(M, Cases), T_) :-
    typeof(Γ,M,T),lcst(Γ,T,variant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|Γ],Mi,Ti_)),Cases,CaseTypes),
    foldl(join(Γ),bot,CaseTypes,T_).
typeof(Γ,ref(M1),ref(T1)) :- typeof(Γ,M1,T1).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), lcst(Γ,T,ref(T1)).
typeof(Γ,deref(M1),bot) :- typeof(Γ,M1,T), lcst(Γ,T,bot).
typeof(Γ,deref(M1),T1) :- typeof(Γ,M1,T), lcst(Γ,T,source(T1)).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), lcst(Γ,T,ref(T1)),typeof(Γ,M2,T2),subtype(Γ,T2,T1).
typeof(Γ,assign(M1,M2),bot) :- typeof(Γ,M1,T), lcst(Γ,T,bot),typeof(Γ,M2,_).
typeof(Γ,assign(M1,M2),unit) :- typeof(Γ,M1,T), lcst(Γ,T,sink(T1)),typeof(Γ,M2,T2),subtyping(Γ,T2,T1).
typeof(Γ,loc(l),_) :- !,fail.
typeof(Γ,try(M1,M2),T) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),join(Γ,T1,T2,T).
typeof(Γ,error,bot).
typeof(Γ,tfn(TX,T1,M2),all(TX,T1,T2)) :- typeof([TX-bTVar(T1)|Γ],M2,T2),!.
typeof(Γ,tapp(M1,T2),T12_) :- typeof(Γ,M1,T1),lcst(Γ,T1,all(X,T11,T12)),subtype(Γ,T2,T11),tsubst(X,T2,T12,T12_).
%typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar(T),R) :- swritef(R,' <: %w',[T]). 
show_bind(Γ,bMAbb(M,none),R) :- typeof(Γ,M,T),swritef(R,' : %w',[T]).
show_bind(Γ,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(Γ,bTAbb(T),' :: *').

run(eval(M),(Γ,St),(Γ,St_)) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,St,M,M_,St_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),(Γ,St),([X-Bind|Γ],St_)) :-
  typeof(Γ,M,T),evalbinding(Γ,St,bMAbb(M,some(T)),Bind,St_),write(X),show_bind(Γ,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),(Γ,St),([X-Bind|Γ],St_)) :-
  typeof(Γ,M,T_),teq(Γ,T_,T),evalbinding(Γ,St,bMAbb(M,some(T)),Bind,St_),show_bind(Γ,Bind,S),write(X),writeln(S).
run(bind(X,Bind),(Γ,St),([X-Bind_|Γ],St_)) :-
  evalbinding(Γ,St,Bind,Bind_,St_),show_bind(Γ,Bind_,S),write(X),writeln(S).

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
