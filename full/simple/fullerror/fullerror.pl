% ------------------------   SUBSTITUTION  ------------------------

let rec subst r s = function
    | MTrue as m -> m
    | MFalse as m -> m
    | MIf(m1,m2,m3) -> MIf(subst r s m1,subst r s m2,subst r s m3)
    | MVar(x) -> if x=r then s else MVar(x)
    | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x r s m2)
    | MApp(m1,m2) -> MApp(subst r s m1, subst r s m2)
    | MTry(m1,m2) -> MTry(subst r s m1,subst r s m2)
    | MError as m -> m
and subst2 x j s t =
  if x=j then t else subst j s t

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | MAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let nv m1 = not(v m1)

let rec eval_context = function
  | MIf(m1,m2,m3) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MIf(f m1, m2,m3))
  | MApp(m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MApp(f m1, m2))
  | MApp(v1,m2) when nv m2 -> let(h,f)=eval_context m2 in (h, fun m2->MApp(v1, f m2))
  | MTry(m1,m2) when nv m1 -> (MTry(m1,m2), fun m1->m1)
  | m1 when nv m1 -> (m1, fun m1 -> m1)
  | _ ->  raise NoRuleApplies

let rec eval1 g = function
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MVar(x) ->
      begin match getb g x with
      | BMAbb(m,_) -> m 
      | _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MTry(MError, m2) -> m2
  | MTry(v1, m2) when v v1 -> v1
  | MTry(m1, m2) -> MTry(eval1 g m1,m2)
  | MError -> raise NoRuleApplies
  | m ->
      match eval_context m with
      | MError,f -> MError
      | h,f when h=m -> raise NoRuleApplies
      | h,f -> f (eval1 g h)

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
  | (TTop,TTop) -> true
  | (TBot,TBot) -> true
  | (TVar(x), t) when istabb g x -> teq g (gettabb g x) t
  | (s,TVar(x)) when istabb g x -> teq g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | _ -> false

let rec subtype g s t =
   teq g s t ||
   match (simplify g s, simplify g t) with
   | (_,TTop) -> true
   | (TBot,_) -> true
   | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
   | (_,_) -> false

let rec join g s t =
  if subtype g s t then t else 
  if subtype g t s then s else
  match (simplify g s, simplify g t) with
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(meet g s1 t1, join g s2 t2)
  | _ -> TTop

and meet g s t =
  if subtype g s t then s else 
  if subtype g t s then t else 
  match (simplify g s, simplify g t) with
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | _ -> TBot

% ------------------------   TYPING  ------------------------

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
      if subtype g (typeof g m1) TBool then
        join g (typeof g m2) (typeof g m3)
      else failwith "guard of conditional not g boolean"
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match simplify g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch" 
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
  | MTry(m1,m2) -> join g (typeof g m1) (typeof g m2)
  | MError -> TBot

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

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

% lambda x:Bot. x;
% lambda x:Bot. x x; 

% lambda x:Top. x;
%  (lambda x:Top. x) (lambda x:Top. x);
% (lambda x:Top->Top. x) (lambda x:Top. x);


% lambda x:Bool. x;
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 

% if error then true else false;


% error true;
% (lambda x:Bool. x) error;

% T = Bool;
% a = true;
% a;

% try error with true;
% try if true then error else true with false;
