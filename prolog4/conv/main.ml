open Syntax

let parse_file filename = 
  let fp = open_in filename in
  Parser.exp Lexer.token (Lexing.from_channel fp)

let parse str =
  Parser.exp Lexer.token (Lexing.from_string str)

let run x =
  (*
    Printf.printf "parse start\n";flush_all();*)
    let ast = parse_file x in
    (*
    Printf.printf "parse end\n";flush_all();*)
    let ast = opconvert ast in
    (*let ast = Varconv.f ast in*)
    let ast = Conv.f ast in
    Printf.printf "%s\n" (show ast)

let () =
  Arg.parse
    []
    (fun x -> run x)
    "Usage: compact filename1 filename2 ..."
