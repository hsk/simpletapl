% ------------------------   SUBSTITUTION  ------------------------

let rec tsubst j s = function
  | TBool -> TBool
  | TNat -> TNat
  | TUnit -> TUnit
  | TFloat -> TFloat
  | TString -> TString
  | TTop -> TTop
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1,tsubst j s t2)
  | TRecord(fieldtys) -> TRecord(List.map (fun (li,ti) -> (li, tsubst j s ti)) fieldtys)

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
    | MTimesfloat(m1,m2) -> MTimesfloat(subst j s m1,subst j s m2)
    | MString _ as m -> m
    | MVar(x) -> if x=j then s else MVar(x)
    | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
    | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
    | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst j s m2)
    | MFix(m1) -> MFix(subst j s m1)
    | MInert(t) -> MInert(t)
    | MAscribe(m1,t1) -> MAscribe(subst j s m1,t1)
    | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,subst j s mi)) fields)
    | MProj(m1,l) -> MProj(subst j s m1,l)
and subst2 x j s t =
  if x=j then t else subst j s t

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | BMAbb(_,Some(t)) -> t
  | BMAbb(_,None) -> failwith ("No type recorded for variable " ^ x)
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | m when n m -> true
  | MUnit -> true
  | MFloat _ -> true
  | MString _ -> true
  | MAbs(_,_,_) -> true
  | MRecord(mf) -> List.for_all (fun (l,m) -> v m) mf
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
  | MAscribe(m1,t) -> MAscribe(eval1 g m1, t)
  | MRecord(mf) ->
      let rec f = function
        | [] -> raise NoRuleApplies
        | (l,vi)::rest when v vi -> (l,vi)::(f rest)
        | (l,mi)::rest -> (l, eval1 g mi)::rest
      in
      MRecord(f mf)
  | MProj((MRecord(mf) as v1), l) when v v1 ->
      begin try List.assoc l mf
      with Not_found -> raise NoRuleApplies
      end
  | MProj(m1, l) -> MProj(eval1 g m1, l)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

let evalbinding g = function
  | BMAbb(m,t) -> BMAbb(eval g m,t)
  | bind -> bind

% ------------------------   SUBTYPING  ------------------------

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
  | _ -> false

let rec subtype g s t =
  teq g s t ||
  match (simplify g s, simplify g t) with
  | (_,TTop) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
  | (TRecord(sf), TRecord(tf)) ->
      List.for_all begin fun (l,t) -> 
        try subtype g (List.assoc l sf) t with Not_found -> false
      end tf
  | (_,_) -> false

let rec join g s t =
  if subtype g s t then t else 
  if subtype g t s then s else
  match (simplify g s, simplify g t) with
  | (TRecord(sf), TRecord(tf)) ->
      let uf = List.find_all (fun (l,_) -> List.mem_assoc l tf) sf in
      TRecord(List.map (fun (l,s) -> (l, join g s (List.assoc l tf))) uf)
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
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | _ -> raise Not_found

% ------------------------   TYPING  ------------------------

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
      begin match simplify g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MLet(x,m1,m2) -> typeof ((x,BVar(typeof g m1))::g) m2
  | MFix(m1) ->
      begin match simplify g (typeof g m1) with
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
      begin match simplify g (typeof g m1) with
      | TRecord(fieldtys) ->
          begin try List.assoc l fieldtys
          with Not_found -> failwith ("label " ^ l ^ " not found")
          end
      | _ -> failwith "Expected record type"
      end

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar -> ""
  | BMAbb(m, None) -> " : " ^ show_t (typeof g m)
  | BMAbb(m, Some(t)) -> " : " ^ show_t t
  | BTAbb(t) -> " :: *"

let _ = 
  let filename = ref "" in
  Arg.parse [] (fun s ->
       if !filename <> "" then failwith "You must specify exactly one input file";
       filename := s
  ) "";
  if !filename = "" then failwith "You must specify an input file";
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
  ) [] (parseFile !filename) 

/* Examples for testing */

%  lambda x:Top. x;
%   (lambda x:Top. x) (lambda x:Top. x);
%  (lambda x:Top->Top. x) (lambda x:Top. x);
%  

% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 


% "hello";

% unit;

% lambda x:A. x;

% let x=true in x;

% {x=true, y=false}; 
% {x=true, y=false}.x;
% {true, false}; 
% {true, false}.1; 


% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

% timesfloat 2.0 3.14159;

% lambda x:Bool. x;
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 

% lambda x:Nat. succ x;
% (lambda x:Nat. succ (succ x)) (succ 0); 

% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);

