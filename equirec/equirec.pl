% ------------------------   SUBSTITUTION  ------------------------

let rec tsubst j s = function
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1, tsubst j s t2)
  | TRec(x,t) -> TRec(x, tsubst2 x j s t)
and tsubst2 x j s t =
  if x=j then t else tsubst j s t

let rec subst j s = function
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x, t1, subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1, subst j s m2)
and subst2 x j s t =
  if x=j then t else subst j s t

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 

% ------------------------   EVALUATION  ------------------------

let rec v = function
  | MAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

let rec compute g = function
  | TRec(x,s1) as s -> tsubst x s s1
  | _ -> raise NoRuleApplies

let rec simplify g t =
  try simplify g (compute g t)
  with NoRuleApplies -> t

let rec teq seen g s t =
  List.mem (s,t) seen ||
  match (s,t) with
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq seen g s1 t1 && teq seen g s2 t2
  | (TRec(x,s1),_) -> teq ((s,t)::seen) g (tsubst x s s1) t
  | (_,TRec(x,t1)) -> teq ((s,t)::seen) g s (tsubst x t t1)
  | _ -> false

let teq g s t = teq [] g s t

% ------------------------   TYPING  ------------------------

let rec typeof g = function
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match simplify g t1 with
      | TArr(t11,t12) ->
          if teq g t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').

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
      Printf.printf "%s%s\n" x (show_bind g bind);
      (x,bind)::g
  ) [] (parseFile !filename) 

% ------------------------   TEST  ------------------------

/* Examples for testing */
%lambda x:A. x;
%lambda f:Rec X.A->A. lambda x:A. f x;

%lambda x:T. x;
%T;
%i : T;
%i;
