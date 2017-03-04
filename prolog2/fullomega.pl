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
tsubst(J,S,ref(T1),ref(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,all(TX,K1,T2),all(TX,K1,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,some(TX,K1,T2),some(TX,K1,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,abs(TX,K1,T2),abs(TX,K1,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,app(TX,T1,T2),app(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
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
subst(J,M,ref(M1), ref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,deref(M1), deref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,assign(M1,M2), assign(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,loc(L), loc(L)).
subst(J,M,tfn(TX,K1,M2),tfn(TX,K1,M2_)) :- subst(J,M,M2,M2_).
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
tmsubst(J,S,ref(M1),ref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,deref(M1),deref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,assign(M1,M2),assign(M1_,M2_)) :- tmsubst(J,S,M2,M2_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,loc(L),loc(L)).
tmsubst(J,S,tfn(TX,K1,M2),tfn(TX,K1,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst(J,S,pack(T1,M2,T3),pack(T1_,M2_,T3_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_),tsubst(J,S,T3,T3_).
tmsubst(J,S,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
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
v(loc(_)).
v(pack(_,V1,_)) :- v(V1).
v(tfn(_,_,_)).

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
eval1(G,St,ref(V1),loc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(G,St,ref(M1),ref(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,deref(loc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(G,St,deref(M1),deref(M1_),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,assign(loc(L),V2),unit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(G,St,assign(V1,M2),assign(V1, M2_),St_) :- v(V1), eval1(G,St,M2,M2_,St_).
eval1(G,St,assign(M1,M2),assign(M1_, M2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,tapp(tfn(X,K,M11),T2),M11_,St_) :- tmsubst(X,T2,M11,M11_).
eval1(G,St,tapp(M1,T2),tapp(M1_,T2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,pack(T1,M2,T3),pack(T1,M2_,T3),St_) :- eval1(G,St,M2,M2_,St_).
eval1(G,St,unpack(_,X,pack(T11,V12,_),M2),M,St) :- v(V12),subst(X,V12,M2,M2_),tmsubst(X,T11,M2_,M).
eval1(G,St,unpack(TX,X,M1,M2),unpack(TX,X,M1_,M2),St_) :- eval1(St,G,M1,M1_,St_).
eval(G,St,M,M_,St_) :- eval1(G,St,M,M1,St1),eval(G,St1,M1,M_,St_).
eval(G,St,M,M,St).

evalbinding(G,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(G,St,M,M_,St_).
evalbinding(G,St,Bind,Bind,St).

% ------------------------   KINDING  ------------------------

gettabb(G,X,T) :- getb(G,X,bTAbb(T,_)).
compute(G,var(X),T) :- gettabb(G,X,T).
compute(G,app(abs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(G,app(T1,T2),T_) :- simplify(G,T1,T1_),simplify2(G,app(T1_,T2),T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,bool,bool).
teq2(G,nat,nat).
teq2(G,unit,unit).
teq2(G,float,float).
teq2(G,string,string).
teq2(G,var(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,var(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,var(X),var(X)).
teq2(G,arr(S1,S2),arr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,record(Sf),record(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(G,S,T)), Tf).
teq2(G,ref(S),ref(T)) :- teq(G,S,T).
teq2(G,all(TX1,K1,S2),all(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,some(TX1,K1,S2),some(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,abs(TX1,K1,S2),abs(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,app(S1,S2),app(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).


kindof(G,T,K) :- kindof1(G,T,K),!.
kindof(G,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(G,var(X),kStar) :- \+member(X-_,G).
kindof1(G,var(X),K) :- getb(G,X,bTVar(K)),!.
kindof1(G,var(X),K) :- !,getb(G,X,bTAbb(_,some(K))).
kindof1(G,arr(T1,T2),kStar) :- !,kindof(G,T1,kStar),kindof(G,T2,kStar).
kindof1(G,record(Tf),kStar) :- maplist([L:S]>>kindof(G,S,kStar),Tf).
kindof1(G,all(TX,K1,T2),kStar) :- !,kindof([TX-bTVar(K1)|G],T2,kStar).
kindof1(G,some(TX,K1,T2),kStar) :- !,kindof([TX-bTVar(K1)|G],T2,kStar).
kindof1(G,abs(TX,K1,T2),kArr(K1,K)) :- !,kindof([TX-bTVar(K1)|G],T2,K).
kindof1(G,app(T1,T2),K12) :- !,kindof(G,T1,kArr(K11,K12)),kindof(G,T2,K11).
kindof1(G,T,kStar).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,zero,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,pred(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,iszero(M1),bool) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,unit,unit).
typeof(G,float(_),float).
typeof(G,timesfloat(M1,M2),float) :- typeof(G,M1,T1),teq(G,T1,float),typeof(G,M2,T2),teq(G,T2,float).
typeof(G,string(_),string).
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- kindof(G,T1,kStar),typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,let(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,fix(M1),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),teq(G,T12,T11).
typeof(G,inert(T),T).
typeof(G,as(M1,T),T) :- kindof(G,T,kStar),typeof(G,M1,T1),teq(G,T1,T).
typeof(G,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,proj(M1,L),T) :- typeof(G,M1,T1),simplify(G,T1,record(Tf)),member(L:T,Tf).
typeof(G,ref(M1),ref(T1)) :- typeof(G,M1,T1).
typeof(G,deref(M1),T1) :- typeof(G,M1,T), simplify(G,T,ref(T1)).
typeof(G,assign(M1,M2),unit) :- typeof(G,M1,T), simplify(G,T,ref(T1)),typeof(G,M2,T2),teq(G,T2,T1).
typeof(G,pack(T1,M2,T),T) :- kindof(G,T,kStar),simplify(G,T,some(Y,K1,T2)),
    kindof(G,T1,K1),
    typeof(G,M2,S2),tsubst(Y,T1,T2,T2_),teq(G,S2,T2_).
typeof(G,unpack(TX,X,M1,M2),T2) :- typeof(G,M1,T1),
      simplify(G,T1,some(_,K,T11)),typeof([X-bVar(T11),(TX-bTVar(K))|G],M2,T2).
typeof(G,tfn(TX,K1,M2),all(TX,K1,T2)) :- typeof([TX-bTVar(K1)|G],M2,T2).
typeof(G,tapp(M1,T2),T12_) :- kindof(G,T2,K2),typeof(G,M1,T1),simplify(G,T1,all(X,K2,T12)),tsubst(X,T2,T12,T12_).
typeof(G,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).
show_bind(G,bTAbb(T,none),R) :- kindof(G,T,K), swritef(R,' :: %w',[K]).
show_bind(G,bTAbb(T,some(K)),R) :- swritef(R,' :: %w',[K]).
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).

run(eval(M),(G,St),(G,St_)) :-
    !,typeof(G,M,T),!,eval(G,St,M,M_,St_),!,writeln(M_:T).
run(bind(X,Bind),(G,St),([X-Bind_|G],St_)) :-
    check_bind(G,Bind,Bind1),
    evalbinding(G,St,Bind1,Bind_,St_),
    write(X),show_bind(G,Bind_,R),writeln(R).
run(someBind(TX,X,M),(G,St),([X-B,TX-bTVar(K)|G],St_)) :-
    !,typeof(G,M,T),
    simplify(G,T,some(_,K,TBody)),
    eval(G,St,M,M_,St_),
    check_someBind(TBody,M_,B),
    writeln(TX),write(X),write(' : '),writeln(TBody).

check_bind(G,bName,bName).
check_bind(G,bTVar(K),bTVar(K)).
check_bind(G,bTAbb(T,none),bTAbb(T,some(K))) :- kindof(G,T,K).
check_bind(G,bTAbb(T,some(K)),bTAbb(T,some(K))) :- kindof(G,T,K).
check_bind(G,bVar(T),bVar(T)).
check_bind(G,bMAbb(M,none), bMAbb(M,some(T))) :- typeof(G,M,T).
check_bind(G,bMAbb(M,some(T)),bMAbb(M,some(T))) :- typeof(G,M,T1), teq(G,T1,T).

check_someBind(TBody,pack(_,T12,_),bMAbb(T12,some(TBody))).
check_someBind(TBody,_,bVar(TBody)).

run(Ls) :- foldl(run,Ls,([],[]),_).

% ------------------------   TEST  ------------------------

% "hello";
:- run([eval(string(hello))]).
% unit;
:- run([eval(unit)]).
% lambda x:A. x;
:- run([eval(fn(x,var('A'),var(x)))]).
% let x=true in x;
:- run([eval(let(x,true,var(x)))]).
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
:- run([bind('T',bTAbb(arr(nat,nat),none)),
        eval(fn(f,var('T'),fn(x,nat,app(var(f),app(var(f),var(x))))))]).
% lambda X. lambda x:X. x;
:- run([eval(tfn('X',kStar,fn(x,var('X'),var(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(tapp(tfn('X',kStar,fn(x,var('X'),var(x))),all('X',kStar,app(var('X',var('X'))))))]).

% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([eval(pack(all('Y',kStar,var('Y')),fn(x,all('Y',kStar,var('Y')),var(x)),some('X',kStar,arr(var('X'),var('X'))) ))]).

% {x=true, y=false};
:- run([eval(record([x=true,y=false])) ]).
% {x=true, y=false}.x;
:- run([eval(proj(record([x=true,y=false]),x)) ]).
% {true, false};
:- run([eval(record([1=true,2=false])) ]).
% {true, false}.1;
:- run([eval(proj(record([1=true,2=false]),1)) ]).
% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
:- run([eval(pack(nat,record([c=zero,f=fn(x,nat,succ(var(x)))]),
         some('X',kStar,record([c:var('X'),f:arr(var('X'),nat)]))))]).

% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);
:- run([eval(unpack('X',ops,pack(nat,record([c=zero,f=fn(x,nat,succ(var(x)))]),some('X',kStar,record([c:var('X'),f:arr(var('X'),nat)]))),app(proj(var(ops),f),proj(var(ops),c))) )]).

:-run([
% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;
bind('Pair',bTAbb(abs('X',kStar,abs('Y',kStar,
  all('R',kStar,arr(arr(var('X'),arr(var('Y'),var('R'))),var('R'))))),none)),
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;
bind(pair,bMAbb(tfn('X',kStar,tfn('Y',kStar,
  fn(x,var('X'),fn(y,var('Y'),
    tfn('R',kStar,
      fn(p,arr(var('X'),arr(var('Y'),var('R'))),
        app(app(var(p),var(x)),var(y)))))))),none)),
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
bind(fst,bMAbb(tfn('X',kStar,tfn('Y',kStar,
  fn(p,app(app(var('Pair'),var('X')),var('Y')),
    app(tapp(var(p),var('X')),
         fn(x,var('X'),fn(y,var('Y'),var(x))) ) ))),none)),
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);
bind(snd,bMAbb(tfn('X',kStar,tfn('Y',kStar,
  fn(p,app(app(var('Pair'),var('X')),var('Y')),
    app(tapp(var(p),var('Y')),
         fn(x,var('X'),fn(y,var('Y'),var(y))) ) ))),none)),
% pr = pair [Nat] [Bool] 0 false;
bind(pr,bMAbb(app(app(tapp(tapp(var(pair),nat),bool),zero),false),none)),
% fst [Nat] [Bool] pr;
eval(app(tapp(tapp(var(fst),nat),bool),var(pr))),
% snd [Nat] [Bool] pr;
eval(app(tapp(tapp(var(snd),nat),bool),var(pr)))
]).

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
