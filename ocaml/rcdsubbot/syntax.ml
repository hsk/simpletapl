type t =
  | TTop
  | TBot
  | TArr of t * t
  | TRecord of (string * t) list

type m =
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m
  | MRecord of (string * m) list
  | MProj of m * string

type b =
  | BName 
  | BVar of t

type c =
  | Eval of m
  | Bind of string * b

let rec show_t = function
  | TArr(m1,m2) -> Printf.sprintf "%s -> %s" (show_t_a m1) (show_t m2)
  | t -> show_t_a t
and show_t_a = function
  | TTop -> "Top"
  | TBot -> "Bot"
  | TRecord(fields) ->
      let pf (li,ti) =
        try let _ = int_of_string li in show_t ti
        with _ -> li ^ ":" ^ show_t ti
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_path m2)
  | m -> show_path m
and show_path = function
  | MProj(m1, l) -> show_path m1 ^ "." ^ l
  | m -> show_a m
and show_a = function
  | MVar(x) -> x
  | MRecord(fields) ->
      let pf (li,mi) =
        try let _ = int_of_string li in show mi
        with _ ->li ^ "=" ^ show mi
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | m -> "(" ^ show m ^ ")"

let rec subst j s = function
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
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
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
