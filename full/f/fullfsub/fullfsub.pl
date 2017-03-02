:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,tBool,tBool).
tsubst(J,S,tNat,tNat).
tsubst(J,S,tUnit,tUnit).
tsubst(J,S,tFloat,tFloat).
tsubst(J,S,tString,tString).
tsubst(J,S,tTop,tTop).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tRecord(Mf),tRecord(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,tSome(TX,T1,T2),tSome(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tAll(TX,T1,T2),tAll(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

let rec subst j s = function
    | MTrue as m -> m
    | MFalse as m -> m
    | MIf(m1,m2,m3) -> MIf(subst j s m1,subst j s m2,subst j s m3)
    | MZero -> MZero
    | MSucc(m1) -> MSucc(subst j s m1)
    | MPred(m1) -> MPred(subst j s m1)
    | MIsZero(m1) -> MIsZero(subst j s m1)
    | MUnit as m -> m
    | MFloat _ as m -> m
    | MTimesfloat(m1,m2) -> MTimesfloat(subst j s m1, subst j s m2)
    | MString _ as m -> m
    | MVar(x) -> if x=j then s else MVar(x)
    | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
    | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
    | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst2 x j s m2)
    | MFix(m1) -> MFix(subst j s m1)
    | MInert(t) -> MInert(t)
    | MAscribe(m1,t1) -> MAscribe(subst j s m1,t1)
    | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,subst j s mi)) fields)
    | MProj(m1,l) -> MProj(subst j s m1,l)
    | MPack(t1,m2,t3) -> MPack(t1,subst j s m2,t3)
    | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,subst2 x j s m1,subst2 x j s m2)
    | MTAbs(tx,t1,m2) -> MTAbs(tx,t1,subst j s m2)
    | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
and subst2 x j s t =
  if x=j then t else subst j s t

let rec tmsubst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(tmsubst j s m1,tmsubst j s m2,tmsubst j s m3)
  | MZero -> MZero
  | MSucc(m1) -> MSucc(tmsubst j s m1)
  | MPred(m1) -> MPred(tmsubst j s m1)
  | MIsZero(m1) -> MIsZero(tmsubst j s m1)
  | MUnit as m -> m
  | MFloat _ as m -> m
  | MTimesfloat(m1,m2) -> MTimesfloat(tmsubst j s m1, tmsubst j s m2)
  | MString _ as m -> m
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst2 x j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MLet(x,m1,m2) -> MLet(x,tmsubst j s m1,tmsubst2 x j s m2)
  | MFix(m1) -> MFix(tmsubst j s m1)
  | MInert(t) -> MInert(tsubst j s t)
  | MAscribe(m1,t1) -> MAscribe(tmsubst j s m1,tsubst j s t1)
  | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,tmsubst j s mi)) fields)
  | MProj(m1,l) -> MProj(tmsubst j s m1,l)
  | MPack(t1,m2,t3) -> MPack(tsubst j s t1,tmsubst j s m2,tsubst j s t3)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,tmsubst2 x j s m1,tmsubst2 x j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)
and tmsubst2 x j s t =
  if x=j then t else tmsubst j s t

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | BMAbb(_,Some(t)) -> t
  | BMAbb(_,None) -> failwith ("No type recorded for variable " ^ x)
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 

(* ------------------------   EVALUATION  ------------------------ *)

let rec n = function
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | m when n m -> true
  | MUnit -> true
  | MFloat _ -> true
  | MString _ -> true
  | MAbs(_,_,_) -> true
  | MRecord(mf) -> List.for_all (fun (l,m) -> v m) mf
  | MPack(_,v1,_) when v v1 -> true
  | MTAbs(_,_,_) -> true
  | _ -> false

let rec eval1 g = function
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MIf(m1,m2,m3) -> MIf(eval1 g m1, m2, m3)
  | MSucc(m1) -> MSucc(eval1 g m1)
  | MPred(MZero) -> MZero
  | MPred(MSucc(nv1)) when n nv1 -> nv1
  | MPred(m1) -> MPred(eval1 g m1)
  | MIsZero(MZero) -> MTrue
  | MIsZero(MSucc(nv1)) when n nv1 -> MFalse
  | MIsZero(m1) -> MIsZero(eval1 g m1)
  | MTimesfloat(MFloat(f1),MFloat(f2)) -> MFloat(f1 *. f2)
  | MTimesfloat((MFloat(f1) as m1),m2) -> MTimesfloat(m1, eval1 g m2) 
  | MTimesfloat(m1,m2) -> MTimesfloat(eval1 g m1, m2) 
  | MVar(x) ->
      begin match getb g x with
      | BMAbb(m,_) -> m 
      | _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | MLet(x,v1,m2) when v v1 -> subst x v1 m2 
  | MLet(x,m1,m2) -> MLet(x, eval1 g m1, m2) 
  | MFix(MAbs(x,_,m12)) as m -> subst x m m12
  | MFix(m1) -> MFix(eval1 g m1)
  | MAscribe(v1,t) when v v1 -> v1
  | MAscribe(m1,t) -> MAscribe(eval1 g m1,t)
  | MRecord(mf) ->
      let rec f = function
        | [] -> raise NoRuleApplies
        | (l, vi)::rest when v vi -> (l, vi)::(f rest)
        | (l, mi)::rest -> (l, eval1 g mi)::rest
      in
      MRecord(f mf)
  | MProj((MRecord(mf) as v1), l) when v v1 ->
      begin try List.assoc l mf
      with Not_found -> raise NoRuleApplies
      end
  | MProj(m1, l) -> MProj(eval1 g m1, l)
  | MTApp(MTAbs(x,_,m11),t2) -> tmsubst x t2 m11
  | MTApp(m1,t2) -> MTApp(eval1 g m1, t2)
  | MPack(t1,m2,t3) -> MPack(t1,eval1 g m2,t3)
  | MUnpack(_,x,MPack(t11,v12,_),m2) when v v12 -> tmsubst x t11 (subst x v12 m2)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,eval1 g m1,m2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

let evalbinding g = function
  | BMAbb(m,t) -> BMAbb(eval g m, t)
  | bind -> bind

% ------------------------   SUBTYPING  ------------------------

let promote g m =
  match m with
  | TVar(x) ->
      begin match getb g x with
      | BTVar(t) -> t
      | _ -> raise NoRuleApplies
      end
  | _ -> raise NoRuleApplies

let istabb g x = 
  try match getb g x with
  | BTAbb(t) -> true
  | _ -> false
  with _ -> false

let gettabb g x = 
  match getb g x with
  | BTAbb(t) -> t
  | _ -> raise NoRuleApplies

let rec compute g = function
  | TVar(x) when istabb g x -> gettabb g x
  | _ -> raise NoRuleApplies

let rec simplify g t =
  try simplify g (compute g t)
  with NoRuleApplies -> t

let rec teq g s t =
  match (simplify g s, simplify g t) with
  | (TBool,TBool) -> true
  | (TNat,TNat) -> true
  | (TUnit,TUnit) -> true
  | (TFloat,TFloat) -> true
  | (TString,TString) -> true
  | (TTop,TTop) -> true
  | (TVar(x), t) when istabb g x -> teq g (gettabb g x) t
  | (s, TVar(x)) when istabb g x -> teq g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TRecord(sf),TRecord(tf)) ->
      List.length sf = List.length tf &&
      List.for_all begin fun (l,t) ->
        try teq g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) -> teq g s1 t1 && teq ((tx1,BName)::g) s2 t2
  | (TSome(tx1,s1,s2),TSome(_,t1,t2)) -> teq g s1 t1 && teq ((tx1,BName)::g) s2 t2
  | _ -> false

let rec subtype g s t =
  teq g s t ||
  match (simplify g s, simplify g t) with
  | (_,TTop) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
  | (TVar(_) as s,t) -> subtype g (promote g s) t
  | (TRecord(sf), TRecord(tf)) ->
      List.for_all begin fun (l,t) -> 
        try subtype g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) ->
      subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
  | (TSome(tx1,s1,s2),TSome(_,t1,t2)) ->
      subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
  | (_,_) -> false

let rec join g s t =
  if subtype g s t then t else 
  if subtype g t s then s else
  match (simplify g s, simplify g t) with
  | (TRecord(sf), TRecord(tf)) ->
      let uf = List.find_all (fun (l,_) -> List.mem_assoc l tf) sf in
      TRecord(List.map (fun (l,s) -> (l, join g s (List.assoc l tf))) uf)
  | (TAll(tx,s1,s2),TAll(_,t1,t2)) ->
      if not(subtype g s1 t1 && subtype g t1 s1) then TTop
      else TAll(tx,s1,join ((tx,BTVar(t1))::g) t1 t2)
  | (TArr(s1,s2),TArr(t1,t2)) ->
      begin try TArr(meet g s1 t1, join g s2 t2)
      with Not_found -> TTop
      end
  | _ -> TTop

and meet g s t =
  if subtype g s t then s else 
  if subtype g t s then t else 
  match (simplify g s, simplify g t) with
  | (TRecord(sf), TRecord(tf)) ->
      let sf =
        List.map begin fun (l,s) -> 
          if List.mem_assoc l tf then (l, meet g s (List.assoc l tf))
          else (l, s)
        end sf
      in
      TRecord(List.append sf (List.find_all (fun (l,_) -> not (List.mem_assoc l sf)) tf))
  | (TAll(tx,s1,s2),TAll(_,t1,t2)) ->
      if not(subtype g s1 t1 && subtype g t1 s1) then raise Not_found else
      TAll(tx,s1,meet ((tx,BTVar(t1))::g) t1 t2)
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | _ -> raise Not_found

% ------------------------   TYPING  ------------------------

let rec lcst g s =
  let s = simplify g s in
  try lcst g (promote g s)
  with NoRuleApplies -> s

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
      if subtype g (typeof g m1) TBool then
        join g (typeof g m2) (typeof g m3)
      else failwith "guard of conditional not g boolean"
  | MZero -> TNat
  | MSucc(m1) ->
      if subtype g (typeof g m1) TNat then TNat
      else failwith "argument of succ is not g number"
  | MPred(m1) ->
      if subtype g (typeof g m1) TNat then TNat
      else failwith "argument of pred is not g number"
  | MIsZero(m1) ->
      if subtype g (typeof g m1) TNat then TBool
      else failwith "argument of iszero is not g number"
  | MUnit -> TUnit
  | MFloat _ -> TFloat
  | MTimesfloat(m1,m2) ->
      if subtype g (typeof g m1) TFloat
      && subtype g (typeof g m2) TFloat then TFloat
      else failwith "argument of timesfloat is not g number"
  | MString _ -> TString
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match lcst g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MLet(x,m1,m2) -> typeof ((x,BVar(typeof g m1))::g) m2
  | MFix(m1) ->
      begin match lcst g (typeof g m1) with
      | TArr(t11,t12) ->
          if subtype g t12 t11 then t12
          else failwith "result of body not compatible with domain"
      | _ -> failwith "arrow type expected"
      end
  | MInert(t) -> t
  | MAscribe(m1,t) ->
     if subtype g (typeof g m1) t then t
     else failwith "body of as-term does not have the expected type"
  | MRecord(mf) -> TRecord(List.map (fun (l,m) -> (l, typeof g m)) mf)
  | MProj(m1, l) ->
      begin match lcst g (typeof g m1) with
      | TRecord(mf) ->
          begin try List.assoc l mf
          with Not_found -> failwith ("label " ^ l ^ " not found")
          end
      | _ -> failwith "Expected record type"
      end
  | MPack(t1,m2,t) ->
      begin match simplify g t with
      | TSome(y,tbound,t2) ->
          if not (subtype g t1 tbound) then failwith "hidden type not g subtype of bound";
          if subtype g (typeof g m2) (tsubst y t1 t2) then t
          else failwith "doesn'm match declared type"
      | _ -> failwith "existential type expected"
      end
  | MUnpack(tx,x,m1,m2) ->
      begin match lcst g (typeof g m1) with
      | TSome(_,tbound,t11) -> typeof ((x,BVar t11)::(tx, BTVar tbound)::g) m2
      | _ -> failwith "existential type expected"
      end
  | MTAbs(tx,t1,m2) -> TAll(tx,t1,typeof ((tx,BTVar(t1))::g) m2)
  | MTApp(m1,t2) ->
      begin match lcst g (typeof g m1) with
      | TAll(x,t11,t12) ->
          if not(subtype g t2 t11) then failwith "type parameter type mismatch";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar(t) -> " : " ^ show_t t
  | BMAbb(m, None) -> " : " ^ show_t (typeof g m)
  | BMAbb(m, Some(t)) -> " : " ^ show_t t
  | BTAbb(t) -> " :: *"

let _ = 
  List.fold_left (fun g -> function
    | Eval(m)->
        let t = typeof g m in
        let m = eval g m in
        Printf.printf "%s : %s\n" (show m) (show_t t);
        g
    | Bind(x,bind) ->
        let bind =
          match bind with
          | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
          | BMAbb(m,Some(t)) ->
            let t' = typeof g m in
            if teq g t' t then BMAbb(m,Some(t))
            else failwith "Type of b does not match declared type"
          | bind -> bind
        in
        let bind = evalbinding g bind in
        Printf.printf "%s%s\n" x (show_bind g bind);
        (x,bind)::g
    | SomeBind(tX,x,m) ->
        match simplify g (typeof g m) with
        | TSome(_,tbound,tbody) ->
            let b =
              match eval g m with
              | MPack(_,t12,_) -> (BMAbb(t12,Some(tbody)))
              | _ -> BVar(tbody)
            in
            Printf.printf "%s\n%s : %s\n" tX x (show_t tbody);
            (x,b)::(tX,BTVar tbound)::g
        | _ -> failwith "existential type expected"
  ) [] (parseFile !filename) 

% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z};
:- run([eval(mApp(mAbs(r,tRecord([x:tArr(tTop,tTop)]),mApp(mProj(mVar(r),x),mProj(mVar(r),x))),
                  mRecord([x=mAbs(z,tTop,mVar(z)),y=mAbs(z,tTop,mVar(z))])))]).
% "hello";
% unit;
% lambda x:A. x;
% let x=true in x;
:- run([eval(mLet(x,mTrue,mVar(x)))]).
% {x=true, y=false};
:- run([eval(mRecord([x=mTrue,y=mFalse])) ]).
% {x=true, y=false}.x;
:- run([eval(mProj(mRecord([x=mTrue,y=mFalse]),x)) ]).
% {true, false};
:- run([eval(mRecord([1=mTrue,2=mFalse])) ]).
% {true, false}.1;
:- run([eval(mProj(mRecord([1=mTrue,2=mFalse]),1)) ]).
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([eval(mIf(mTrue,mRecord([x=mTrue,y=mFalse,a=mFalse]),mRecord([y=mFalse,x=mRecord([]),b=mFalse])))]).
% timesfloat 2.0 3.14159;
:- run([eval(mTimesfloat(mFloat(2.0),mFloat(3.14159))) ]).
% lambda X. lambda x:X. x; 
:- run([eval(mTAbs('X',mAbs(x,'X',mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
% lambda X<:Top->Top. lambda x:X. x x; 
% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true);
% lambda x:Nat. succ x;
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
%  {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);

:- halt.
