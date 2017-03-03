%:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPrec(M1),mPrec(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mAbs(_,_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
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
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,mApp(V1,M2),mApp(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_,M2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

type nextuvar = NextUVar of string * (unit -> nextuvar)

let uvargen =
  let rec f i () =
    NextUVar("?X" ^ string_of_int i, f (i+1))
  in f 0

let rec recon g nextuvar m =
    match m with
    | MVar(x) -> (gett g x, nextuvar, [])
    | MAbs(x, t1, m2) ->
        let (t2,nextuvar2,constr2) = recon ((x,BVar(t1))::g) nextuvar m2 in
        (TArr(t1, t2), nextuvar2, constr2)
    | MApp(m1,m2) ->
        let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
        let (t2,nextuvar2,constr2) = recon g nextuvar1 m2 in
        let NextUVar(tx,nextuvar') = nextuvar2() in
        let newconstr = [t1,TArr(t2,TVar(tx))] in
        ((TVar(tx)), nextuvar', List.concat [newconstr; constr1; constr2])
    | MZero -> (TNat, nextuvar, [])
    | MSucc(m1) ->
        let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
        (TNat, nextuvar1, (t1,TNat)::constr1)
    | MPred(m1) ->
        let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
        (TNat, nextuvar1, (t1,TNat)::constr1)
    | MIsZero(m1) ->
        let (t1,nextuvar1,constr1) = recon g nextuvar m1 in
        (TBool, nextuvar1, (t1,TNat)::constr1) 
    | MTrue -> (TBool, nextuvar, [])
    | MFalse -> (TBool, nextuvar, [])
    | MIf(m1,m2,m3) ->
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
    | TVar(s) -> if s = tx then t else TVar(s)
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

  List.fold_left (fun (g,nextuvar,constr) -> function
    | Eval(m)->
      let (t,nextuvar',constr_t) = typeof g nextuvar constr m in
      let m = eval g m in
      Printf.printf "%s : %s\n" (show m) (show_t t);
      (g,nextuvar',constr_t)
    | Bind(x,bind) ->
      Printf.printf "%s%s\n" x (show_bind g bind);
      ((x,bind)::g, uvargen, constr)
  ) ([],uvargen,[]) (parseFile !filename) 

% ------------------------   TEST  ------------------------

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

% if true then false else true;
:- run([eval(mIf(mTrue,mFalse,mTrue))]).
% if true then 1 else 0;
:- run([eval(mIf(mTrue,mSucc(mZero),mZero))]).
% (lambda x:Nat. x) 0;
:- run([eval(mApp(mAbs(x,tNat,mVar(x)),mZero))]).

:- halt.
