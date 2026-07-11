(** Lexer for named CoC syntax.  Keywords are case-sensitive (e.g. [Set],
    [Axiom], [Extract]).  Supports nested [(* ... *)] comments. *)
{
open Parser

let keyword_table = Hashtbl.create 17
let () = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
  [ "Set", SET; "Prop", PROP; "Kind", KIND;
    "fun", FUN; "forall", FORALL;
    "let", LET; "in", IN;
    "Quit", QUIT; "Axiom", AXIOM; "Infer", INFER;
    "Check", CHECK; "Delete", DELETE; "List", LIST;
    "Help", HELP; "Extract", EXTRACT; "Definition", DEFINITION ]
}

let white = [' ' '\t' '\r']
let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident_char = letter | digit | ['_' '\'']

rule token = parse
  | '\n'          { Lexing.new_line lexbuf; token lexbuf }
  | white+        { token lexbuf }
  | "(*"          { comment 1 lexbuf; token lexbuf }
  | "->"          { ARROW }
  | "=>"          { DARROW }
  | ":="          { ASSIGN }
  | '('           { LPAREN }
  | ')'           { RPAREN }
  | ':'           { COLON }
  | ','           { COMMA }
  | '.'           { DOT }
  | '_'           { UNDERSCORE }
  | (letter ident_char*) as s
    { try Hashtbl.find keyword_table s with Not_found -> IDENT s }
  | eof           { EOF }
  | _ as c        { failwith (Printf.sprintf "Illegal character '%c'" c) }

and comment depth = parse
  | "(*"          { comment (depth + 1) lexbuf }
  | "*)"          { if depth > 1 then comment (depth - 1) lexbuf }
  | '\n'          { Lexing.new_line lexbuf; comment depth lexbuf }
  | _             { comment depth lexbuf }
  | eof           { failwith "Unterminated comment" }
