type t =
  | TBool
  | TNat
  | TUnit
  | TString
  | TFloat
  | TTop
  | TBot
  | TVar of string
  | TArr of t * t
  | TRecord of (string * t) list
  | TVariant of (string * t) list
  | TRef of t
  | TSource of t
  | TSink of t
  | TAll of string * t * t

type m =
  | MTrue
  | MFalse
  | MIf of m * m * m
  | MZero
  | MSucc of m
  | MPred of m
  | MIsZero of m
  | MUnit
  | MFloat of float
  | MTimesfloat of m * m
  | MString of string
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m
  | MLet of string * m * m
  | MFix of m
  | MInert of t
  | MAscribe of m * t
  | MRecord of (string * m) list
  | MProj of m * string
  | MCase of m * (string * (string * m)) list
  | MTag of string * m * t
  | MLoc of int
  | MRef of m
  | MDeref of m 
  | MAssign of m * m
  | MError
  | MTry of m * m
  | MTAbs of string * t * m
  | MTApp of m * t

type b =
  | BName 
  | BVar of t
  | BTVar of t
  | BMAbb of m * (t option)
  | BTAbb of t

type c =
  | Eval of m
  | Bind of string * b

let rec show_t = function
  | TRef(t) -> "Ref " ^ show_t_a t
  | TSource(t) -> "Source " ^ show_t_a t
  | TSink(t) -> "Sink " ^ show_t_a t
  | TAll(x, TTop, t2) -> Printf.sprintf "All %s.%s" x (show_t t2)
  | TAll(x, t1, t2) -> Printf.sprintf "All %s<:%s.%s" x (show_t t1) (show_t t2)
  | t -> show_t_arr t
and show_t_arr = function
  | TArr(m1,m2) -> Printf.sprintf "%s -> %s" (show_t_a m1) (show_t_arr m2)
  | t -> show_t_a t
and show_t_a = function
  | TBool -> "Bool"
  | TNat -> "Nat"
  | TUnit -> "Unit"
  | TFloat -> "Float"
  | TString -> "String"
  | TTop -> "Top"
  | TBot -> "Bot"
  | TVar(x) -> x
  | TRecord(fields) ->
      let pf (li,ti) =
        try let _ = int_of_string li in show_t ti
        with _ -> li ^ ":" ^ show_t ti
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | TVariant(fields) ->
      "<" ^ String.concat ", " (List.map (fun (li,ti) -> li ^ ":" ^ show_t ti) fields) ^ ">"
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (show m1) (show m2) (show m3)
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | MLet(x, m1, m2) -> "let " ^ x ^ " = " ^ show m1 ^ " in " ^ show m2
  | MCase(m, cases) ->
      let pc (li,(xi,mi)) =
        "<" ^ li ^ "=" ^ xi ^ ">==>" ^ show_app mi
      in
      "case " ^ show m ^ " of " ^ String.concat " | " (List.map pc cases);
  | MTry(m1, m2) -> Printf.sprintf "try %s with %s" (show m1) (show m2)
  | MAssign (m1, m2) -> show m1 ^ " := " ^ show m2
  | MTAbs(x,TTop,m2) -> Printf.sprintf "lambda %s.%s" x (show m2)
  | MTAbs(x,t1,m2) -> Printf.sprintf "lambda %s<:%s.%s" x (show_t t1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_path m2)
  | MSucc(m1) when not (n m1) -> Printf.sprintf "succ %s" (show_path m1)
  | MPred(m1) -> Printf.sprintf "pred %s" (show_path m1)
  | MIsZero(m1) -> Printf.sprintf "iszero %s" (show_path m1)
  | MTimesfloat(m1,m2) -> "timesfloat " ^ show_path m1 ^ " " ^ show_path m2
  | MFix(m1) -> "fix " ^ show_path m1
  | MLoc i -> "loc " ^ string_of_int i
  | MRef m1 -> "ref " ^ show_path m1
  | MDeref m1 -> "!" ^ show_path m1
  | MTApp(m1, t2) -> Printf.sprintf "%s [%s]" (show_app m1) (show_t t2)
  | m -> show_path m
and show_path = function
  | MProj(m1, l) -> show_path m1 ^ "." ^ l
  | m -> show_as m
and show_as = function
  | MAscribe(m1,t1) -> show_a m1 ^ " as " ^ show_t t1
  | m -> show_a m
and show_a = function
  | MTrue -> "true"
  | MFalse -> "false"
  | MUnit -> "unit"
  | MFloat(s) ->  string_of_float s
  | MString s -> "\"" ^ s ^ "\""
  | MVar(x) -> x
  | MInert(t) -> "inert[" ^ show_t t ^ "]"
  | MRecord(fields) ->
      let pf (li,mi) =
        try let _ = int_of_string li in show mi
        with _ ->li ^ "=" ^ show mi
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | MTag(l, m, t) -> "<" ^ l ^ "=" ^ show m ^ "> as " ^ show_t t
  | MError -> "error"
  | m when n m ->
      let rec f n = function
        | MZero -> string_of_int n
        | MSucc(s) -> f (n+1) s
        | _ -> assert false
      in
      f 0 m
  | m -> "(" ^ show m ^ ")"
and n = function
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec tsubst j s = function
  | TBool -> TBool
  | TNat -> TNat
  | TUnit -> TUnit
  | TFloat -> TFloat
  | TString -> TString
  | TTop -> TTop
  | TBot -> TBot
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1,tsubst j s t2)
  | TRecord(fieldtys) -> TRecord(List.map (fun (li,ti) -> (li, tsubst j s ti)) fieldtys)
  | TVariant(fieldtys) -> TVariant(List.map (fun (li,ti) -> (li, tsubst j s ti)) fieldtys)
  | TRef(t1) -> TRef(tsubst j s t1)
  | TSource(t1) -> TSource(tsubst j s t1)
  | TSink(t1) -> TSink(tsubst j s t1)
  | TAll(tx,t1,t2) -> TAll(tx,tsubst j s t1,tsubst j s t2)

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
  | MTag(l,m1,t) -> MTag(l, subst j s m1, t)
  | MCase(m,cases) -> MCase(subst j s m, List.map (fun (li,(xi,mi)) -> (li, (xi,subst2 xi j s mi))) cases)
  | MRef(m1) -> MRef(subst j s m1)
  | MDeref(m1) -> MDeref(subst j s m1)
  | MAssign(m1,m2) -> MAssign(subst j s m1,subst j s m2)
  | MLoc(l) as m -> m
  | MTry(m1,m2) -> MTry(subst j s m1,subst j s m2)
  | MError as m -> m
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
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MLet(x,m1,m2) -> MLet(x,tmsubst j s m1,tmsubst j s m2)
  | MFix(m1) -> MFix(tmsubst j s m1)
  | MInert(t) -> MInert(tsubst j s t)
  | MAscribe(m1,t1) -> MAscribe(tmsubst j s m1,tsubst j s t1)
  | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,tmsubst j s mi)) fields)
  | MProj(m1,l) -> MProj(tmsubst j s m1,l)
  | MTag(l,m1,t) -> MTag(l, tmsubst j s m1, tsubst j s t)
  | MCase(m,cases) -> MCase(tmsubst j s m, List.map (fun (li,(xi,mi)) -> (li, (xi,tmsubst j s mi))) cases)
  | MRef(m1) -> MRef(tmsubst j s m1)
  | MDeref(m1) -> MDeref(tmsubst j s m1)
  | MAssign(m1,m2) -> MAssign(tmsubst j s m1,tmsubst j s m2)
  | MLoc(l) as m -> m
  | MTry(m1,m2) -> MTry(tmsubst j s m1,tmsubst j s m2)
  | MError as m -> m
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | BMAbb(_,Some(t)) -> t
  | BMAbb(_,None) -> failwith ("No type recorded for variable " ^ x)
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
