open Syntax
open Core

let parseFile filename =
  let fp = open_in filename in
  let m = Parser.p Lexer.main (Lexing.from_channel fp) in
  Parsing.clear_parser();
  close_in fp;
  m

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar(t) -> " <: " ^ show_t t
  | BTAbb(t, None) -> " :: " ^ show_kind (kindof g t)
  | BTAbb(t, Some(k)) -> " :: " ^ show_kind k
  | BMAbb(m, None) -> " : " ^ show m
  | BMAbb(m, Some(t)) -> " : " ^ show_t t

let alreadyImported = ref []

let rec process_file (g,store) filename =
  if List.mem filename !alreadyImported then (g,store) else
  begin
    alreadyImported := filename :: !alreadyImported;
    List.fold_left (fun (g,store) -> function
      | Eval(m)->
          let t = typeof g m in
          let (m,store') = eval g store m in
          Printf.printf "%s : %s\n" (show m) (show_t t);
          (g,store')
      | Bind(x,bind) ->
          let bind =
            match bind with
            | BName -> BName
            | BTVar(k) -> BTVar(k)
            | BTAbb(t,None) -> BTAbb(t,Some(kindof g t))
            | BVar(t) -> BVar(t)
            | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
            | BMAbb(m,Some(t)) ->
                if teq g (typeof g m) t then BMAbb(m,Some(t))
                else failwith "Type of b does not match declared type"
            | BTAbb(t,Some(k)) ->
                if k = kindof g t then BTAbb(t,Some(k))
                else failwith "Kind of b does not match declared kind"
          in
          let (bind,store) = evalbinding g store bind in
          Printf.printf "%s%s\n" x (show_bind g bind);
          ((x,bind)::g,store)
      | SomeBind(tx,x,m) ->
          let t = typeof g m in
          begin match simplify g t with
          | TSome(_,k,tbody) ->
              let (t',store') = eval g store m in
              let b =
                match t' with
                | MPack(_,t12,_) -> BMAbb(t12,Some(tbody))
                | _ -> BVar(tbody)
              in
              Printf.printf "%s\n%s : %s\n" tx x (show_t tbody);
              ((x,b)::(tx,BTVar k)::g, store')
          | _ -> failwith "existential type expected"
          end
      | Import(f) -> process_file (g,store) f 
    ) (g,store) (parseFile filename)
  end

let p = ref false

let _ = 
  let filename = ref "" in
  Arg.parse [
    "-p",Arg.Unit(fun () -> p:=true),"show prolog programs"
  ] (fun s ->
       if !filename <> "" then failwith "You must specify exactly one input file";
       filename := s
  ) "";
  if !filename = "" then failwith "You must specify an input file";
  if !p then Prolog.convert (parseFile !filename) else
  process_file ([],[]) !filename |> ignore
