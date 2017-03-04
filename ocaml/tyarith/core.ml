open Syntax

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec n m =
  match m with
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec v m =
  match m with
  | MTrue -> true
  | MFalse -> true
  | m when n m -> true
  | _ -> false

let rec eval1 m =
  match m with
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MIf(m1,m2,m3) -> MIf(eval1 m1, m2, m3)
  | MSucc(m1) -> MSucc(eval1 m1)
  | MPred(MZero) -> MZero
  | MPred(MSucc(nv1)) when n nv1 -> nv1
  | MPred(m1) -> MPred(eval1 m1)
  | MIsZero(MZero) -> MTrue
  | MIsZero(MSucc(nv1)) when n nv1 -> MFalse
  | MIsZero(m1) -> MIsZero(eval1 m1)
  | _ -> raise NoRuleApplies

let rec eval m =
  try eval (eval1 m) with NoRuleApplies -> m

(* ------------------------   TYPING  ------------------------ *)

let rec typeof m =
  match m with
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
     if typeof m1 = TBool then
       let t2 = typeof m2 in
       if t2 = typeof m3 then t2
       else failwith "arms of conditional have different types"
     else failwith "guard of conditional not g boolean"
  | MZero -> TNat
  | MSucc(m1) ->
      if typeof m1 = TNat then TNat
      else failwith "argument of succ is not g number"
  | MPred(m1) ->
      if typeof m1 = TNat then TNat
      else failwith "argument of pred is not g number"
  | MIsZero(m1) ->
      if typeof m1 = TNat then TBool
      else failwith "argument of iszero is not g number"
