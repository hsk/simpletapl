:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPrec(M1),mPrec(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1,M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mAbs(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mIf(mTrue,M2,_),M2).
eval1(G,mIf(mFalse,_,M3),M3).
eval1(G,mIf(M1,M2,M3),mIf(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,mSucc(M1),mSucc(M1_)) :- eval1(G,M1,M1_).
eval1(G,mPred(mZero),mZero).
eval1(G,mPred(mSucc(N1)),N1) :- n(N1).
eval1(G,mPred(M1),mPred(M1_)) :- eval1(G,M1,M1_).
eval1(G,mIsZero(mZero),mTrue).
eval1(G,mIsZero(mSucc(N1)),mFalse) :- n(N1).
eval1(G,mIsZero(M1),mIsZero(M1_)) :- eval1(G,M1,M1_).
eval1(G,mApp(mAbs(X,_,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mLet(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,mLet(X,M1,M2),mLet(X,M1_,M2)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

% type nextuvar = nextUVar of string * (unit -> nextuvar)

nextuvar(I,S,I_) :- swritef(S,"?X%d",[I]), I_ is I + 1.

recon(G,Cnt,mVar(X),T,Cnt,[]) :- gett(G,X,T).
recon(G,Cnt,mAbs(X, some(T1), M2),tArr(T1,T2),Cnt_,Constr_) :-
    recon([X-bVar(T1)|G],Cnt,M2,T2,Cnt_,Constr_).
recon(G,Cnt,mAbs(X, none, M2),tArr(tVar(U),T2),Cnt2,Constr2) :-
    recon([X-bVar(tVar(U)))|G], Cnt_, M2,T2,Cnt2,Constr2).
recon(G,Cnt,mApp(M1,M2),tVar(TX),Cnt_, Constr_) :-
    recon(G,Cnt,M1,T1,Cnt1,Constr1),
    recon(G,Cnt1,M2,T2,Cnt2,Constr2),
    nextuvar(Cnt2,TX,Cnt_),
    flatten([[T1-tArr(T2,tVar(TX))],Constr1,Constr2], Constr_).
recon(G,Cnt,mLet(X, M1, M2),T_,Cnt_,Constr_) :- v(M1), subst(X,M1,M2,M2_),recon(G, Cnt, M2_,T_,Cnt_,Constr_).
recon(G,Cnt,mLet(X, M1, M2),T2,Cnt2,Constr_) :-
    recon(G,Cnt,M1,T1,Cn1,Constr1),
    recon([X-bVar(T1)|G], Cnt1, M2,T2,Cnt2,Constr2),
    flatten([Constr1,Constr2],Constr_).
recon(G,Cnt,mZero,tNat, Cnt, []).
recon(G,Cnt,mSucc(m1)) :-
      let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
      (TNat, nextuvar1, (t1,TNat)::constr1)
recon(G,Cnt,mPred(m1)) :-
      let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
      (TNat, nextuvar1, (t1,TNat)::constr1)
recon(G,Cnt,mIsZero(m1)) :-
      let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
      (TBool, nextuvar1, (t1,TNat)::constr1) 
recon(G,Cnt,mTrue) :- (TBool, nextuvar, [])
recon(G,Cnt,mFalse) :- (TBool, nextuvar, [])
recon(G,Cnt,mIf(m1,m2,m3)) :-
      let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
      let (t2,nextuvar2,constr2) = recon g nextuvar1 m2 in
      let (t3,nextuvar3,constr3) = recon g nextuvar2 m3 in
      let newconstr = [(t1,TBool); (t2,t3)] in
      (t3, nextuvar3, List.concat [newconstr; constr1; constr2; constr3])

let substinty tx t s =
  let rec f s =
    match s with
    | TArr(s1,s2) -> TArr(f s1, f s2)
    | TNat -> TNat
    | TBool -> TBool 
    | TVar(s) -> if s=tx then t else TVar(s)
  in
  f s

let applysubst constr t =
  List.fold_left begin fun s -> function
    | (TVar(tx),tc2) -> substinty tx tc2 s
    | _ -> assert false
  end t (List.rev constr)

let substinconstr tx t constr =
  List.map begin fun (s1,s2) ->
    (substinty tx t s1, substinty tx t s2)
  end constr

let occursin tx t =
  let rec o t =
    match t with
    | TArr(t1,t2) -> o t1 || o t2
    | TNat -> false
    | TBool -> false
    | TVar(s) -> s = tx
  in
  o t

let unify g msg constr =
  let rec u constr =
    match constr with
    | [] -> []
    | (s,TVar(tx)) :: rest ->
        if s = TVar(tx) then u rest
        else if occursin tx s then failwith (msg ^ ": circular constraints")
        else List.append (u (substinconstr tx s rest)) [(TVar(tx),s)]
    | (TVar(tx),t) :: rest ->
        if t = TVar(tx) then u rest
        else if occursin tx t then failwith (msg ^ ": circular constraints")
        else List.append (u (substinconstr tx t rest)) [(TVar(tx),t)]
    | (TNat,TNat) :: rest -> u rest
    | (TBool,TBool) :: rest -> u rest
    | (TArr(s1,s2),TArr(t1,t2)) :: rest -> u ((s1,t1) :: (s2,t2) :: rest)
    | (s,t)::rest -> failwith "Unsolvable constraints"
  in
  u constr

let typeof g nextuvar constr m =
  let (t,nextuvar',constr_t) = recon g nextuvar m in
  let constr = List.append constr constr_t in
  let constr = unify g "Could not simplify constraints" constr in
  let t = applysubst constr t in
  (t,nextuvar',constr)

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),(G,Cnt,Constr),(G,Cnt_,Constr_)) :-
  !,typeof(G,Cnt,Constr,M,T,Cnt_,Constr_),!,eval(G,M,M_),!,  writeln(M_:T).
run(bind(X,Bind),(G,Cnt,Constr),([X-Bind_|G],Cnt,Constr)) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,([],0,[]),_).

% ------------------------   TEST  ------------------------

% let x=true in x;
:- run([eval(mLet(x,mTrue,mVar(x)))]).
% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]).
% lambda x:Nat. succ x;
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
% lambda x:A. x;
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
% (lambda x:X. lambda y:X->X. y x);
:- run([eval(mAbs(x,tVar('X'), mAbs(y,tArr(tVar('X'),tVar('X')),mApp(mVar(y),mVar(x)))))]). 
% (lambda x:X->X. x 0) (lambda y:Nat. y); 
:- run([eval(mApp(mAbs(x,tArr(tVar('X'),tVar('X')),mApp(mVar(x),mZero)), mAbs(y,tNat,mVar(y))))]). 
% (lambda x. x 0);
:- run([eval(mAbs(x,mApp(mVar(x),none,mZero))) ]). 
% let f = lambda x. x in (f f) (f 0);
:- run([eval(mLet(f,mAbs(x,mApp(mVar(x),none,mVar(x))),mApp(mApp(mVar(f),mVar(f)),mApp(mVar(f),mZero)))) ]). 
% let g = lambda x. 1 in g (g g);
:- run([eval(mLet(g,mAbs(x,mSucc(mZero)),mApp(mVar(g),mApp(mVar(g),mVar(g))))) ]). 

:- halt.