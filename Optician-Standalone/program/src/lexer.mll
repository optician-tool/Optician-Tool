{
open Lexing
open Parser

exception Lexer_error of string

let reserved_words : (string * Parser.token) list =
  [ ("typedef", TYPEDEF)
  ; ("abstract", ABSTRACT)
  ; ("test", TEST)
  ; ("matches", MATCHES) ]

let symbols : (string * Parser.token) list =
  [ ("<=>", LEFTRIGHTFATARR)
  ; ("<->", LEFTRIGHTARR)
  ; (",", COMMA)
  ; ("*", STAR)
  ; ("|", PIPE)
  ; ("+", PLUS)
  ; ("(", LPAREN)
  ; (")", RPAREN)
  ; ("{", LBRACE)
  ; ("}", RBRACE)
  ; ("=", EQ)
  ; (".", DOT)
  ; ("/", SLASH)
  ; ("\\", BACKSLASH)
  ; ("-", HYPHEN)
  ; ("[", LBRACKET)
  ; ("]", RBRACKET)
  ; (";", SEMI)
  ]

let create_token lexbuf =
  let str = lexeme lexbuf in
  match Stdlib.lookup str reserved_words with
  | None   -> LID str
  | Some t -> t

let create_symbol lexbuf =
  let str = lexeme lexbuf in
  match Stdlib.lookup str symbols with
  | None   -> raise @@ Lexer_error ("Unexpected token: " ^ str)
  | Some t -> t

let remove_quotes lexbuf =
  let str = lexeme lexbuf in
  let len = String.length str in
  String.sub str 1 (len-2)
}


let newline    = '\n' | ('\r' '\n') | '\r'
let whitespace = ['\t' ' ']
let string = ('"''"') | ('"' ("\\\"" | [^'"'])* '"')
let lowercase  = ['a'-'z']
let uppercase  = ['A'-'Z']
let character  = uppercase | lowercase
let digit      = ['0'-'9']

rule token = parse
  | eof   { EOF }
  | "(*" {comments 0 lexbuf}
  | whitespace+ | newline+    { token lexbuf }
  | lowercase (digit | character | '_')* { create_token lexbuf }
  | uppercase (digit | character | '_')* { UID (lexeme lexbuf) }
  | '?' | "|>" | '=' | "->" | "=>" | '*' | ',' | ':' | ';' | '|' | '+' | '(' | ')'
  | '{' | '}' | '[' | ']' | '_' | '.' | "<=>" | "<->" | "/"
  | "' '" | "\\" | ":" | ">" | "<" | "-" | "\\n" | "[" | "]" | ";" | "#"
    { create_symbol lexbuf }
  | string { STR (remove_quotes lexbuf) }
  | _ as c { raise @@ Lexer_error ("Unexpected character: " ^ Char.escaped c) }

and comments level = parse
  | "*)" { if level = 0 then token lexbuf
	   else comments (level-1) lexbuf }
  | "(*" { comments (level+1) lexbuf}
  | [^ '\n'] { comments level lexbuf }
  | "\n" { comments level lexbuf }
  | eof	 { failwith "Comments are not closed" }
