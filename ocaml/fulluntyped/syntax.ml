type m =
  | MTrue
  | MFalse
  | MIf of m * m * m
  | MZero
  | MSucc of m
  | MPred of m
  | MIsZero of m
  | MFloat of float
  | MTimesfloat of m * m
  | MString of string
  | MVar of string
  | MAbs of string * m
  | MApp of m * m
  | MLet of string * m * m
  | MRecord of (string * m) list
  | MProj of m * string

type b =
  | BName 
  | BMAbb of m

type c =
  | Eval of m
  | Bind of string * b

let rec show = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (show m1) (show m2) (show m3)
  | MAbs(x,m2) -> Printf.sprintf "lambda %s.%s" x (show m2)
  | MLet(x, m1, m2) -> "let " ^ x ^ " = " ^ show m1 ^ " in " ^ show m2
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_path m2)
  | MSucc(m1) when not (n m1) -> Printf.sprintf "succ %s" (show_path m1)
  | MPred(m1) -> Printf.sprintf "pred %s" (show_path m1)
  | MIsZero(m1) -> Printf.sprintf "iszero %s" (show_path m1)
  | MTimesfloat(m1,m2) -> "timesfloat " ^ show_path m1 ^ " " ^ show_path m2
  | m -> show_path m
and show_path = function
  | MProj(m1, l) -> show_path m1 ^ "." ^ l
  | m -> show_a m
and show_a = function
  | MTrue -> "true"
  | MFalse -> "false"
  | MFloat(s) ->  string_of_float s
  | MVar(x) -> x
  | MRecord(fields) ->
      let pf (li,mi) =
        try let _ = int_of_string li in show mi
        with _ ->li ^ "=" ^ show mi
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | MString s -> "\"" ^ s ^ "\""
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

let rec subst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(subst j s m1,subst j s m2,subst j s m3)
  | MZero -> MZero
  | MSucc(m1) -> MSucc(subst j s m1)
  | MPred(m1) -> MPred(subst j s m1)
  | MIsZero(m1) -> MIsZero(subst j s m1)
  | MFloat _ as m -> m
  | MTimesfloat(m1,m2) -> MTimesfloat(subst j s m1,subst j s m2)
  | MString _ as m -> m
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,m2) -> MAbs(x,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst2 x j s m2)
  | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,subst j s mi)) fields)
  | MProj(m1,l) -> MProj(subst j s m1,l)
and subst2 x j s t =
  if x=j then t else subst j s t

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)
