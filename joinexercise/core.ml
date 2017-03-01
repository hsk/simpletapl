open Syntax

(* ------------------------   EVALUATION  ------------------------ *)

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | MAbs(_,_,_) -> true
  | MRecord(mf) -> List.for_all (fun (l,m) -> v m) mf
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MIf(m1,m2,m3) -> MIf(eval1 g m1, m2, m3)
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
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
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

(* ------------------------   SUBTYPING  ------------------------ *)

let rec subtype s t =
  s = t ||
  match (s,t) with
  | (_,TTop) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> subtype t1 s1 && subtype s2 t2
  | (TRecord(sf), TRecord(tf)) ->
      List.for_all begin fun (l,t) -> 
        try subtype (List.assoc l sf) t with Not_found -> false
      end tf
  | (_,_) -> false

let rec join s t =
  (* Write me *) assert false

and meet s t =
  (* Write me *) assert false

(* ------------------------   TYPING  ------------------------ *)

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) -> (* write me *) assert false
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match t1 with
      | TArr(t11,t12) ->
          if subtype t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MRecord(mf) -> TRecord(List.map (fun (l,m) -> (l, typeof g m)) mf)
  | MProj(m1, l) ->
      begin match (typeof g m1) with
      | TRecord(fieldtys) ->
          begin try List.assoc l fieldtys
          with Not_found -> failwith ("label " ^ l ^ " not found")
          end
      | _ -> failwith "Expected record type"
      end
