%{
open String_utilities
open Lang
%}

%token <string> LID   (* lowercase identifiers *)
%token <string> UID   (* uppercase identifiers *)
%token <string> STR   (* string identifiers *)

(* integer constants translated to O, S(O), S(S(O)), etc. *)

%token TYPEDEF    (* typedef *)
%token ABSTRACT   (* abstract *)
%token TEST       (* test *)
%token MATCHES    (* matches *)

%token LEFTRIGHTFATARR (* <=> *)
%token LEFTRIGHTARR    (* <-> *)
%token COMMA      (* , *)
%token STAR       (* * *)
%token PIPE       (* | *)
%token PLUS       (* + *)
%token LPAREN     (* ( *)
%token RPAREN     (* ) *)
%token LBRACE     (* { *)
%token RBRACE     (* } *)
%token EQ         (* = *)
%token DOT        (* . *)
%token SLASH      (* / *)
%token BACKSLASH  (* \ *)
%token HYPHEN      (* - *)
%token LBRACKET   (* [ *)
%token RBRACKET   (* ] *)
%token SEMI       (* ; *)
%token EOF

%start <Lang.program> program

%%

program:
  | d=decl p=program
    { (d::p) }
  | EOF
    { [] }

decl:
  | d=defn
    { DeclRegexCreation d }
  | s=specification
    { DeclSynthesizeLens s}
  | TEST r=regex MATCHES s=str SEMI SEMI
    { DeclTestString (r,s) }
  | TEST n=LID exs=examples SEMI SEMI
    { DeclTestLens (Id.make n,exs) }

defn:
  | TYPEDEF u=UID EQ r=regex SEMI SEMI
    { (Id.make u,r,true) }
  | ABSTRACT u=UID EQ r=regex SEMI SEMI
    { (Id.make u,r,false) }

specification:
  |  n=LID EQ LBRACKET r1=regex LEFTRIGHTFATARR r2=regex es=examples RBRACKET
    { (Id.make n,r1,r2,es) }

(***** Regexes {{{ *****)

regex:
  | r=regex_l0 { r }

regex_l0:
  | r1=regex_l1 PIPE r2=regex_l0 { Regex.RegExOr (r1,r2) }
  | r=regex_l1 { r }

regex_l1:
  | r1=regex_l2 r2=regex_l1 { Regex.RegExConcat (r1,r2) }
  | r=regex_l2 { r }

regex_l2:
  | r=regex_l2 STAR { Regex.RegExStar r }
  | r=regex_l2 PLUS { Regex.RegExConcat(r, Regex.RegExStar r) }
  | r=regex_l3 { r }

regex_l3:
  | s=base { Regex.RegExBase s }
  | LPAREN r=regex_l0 RPAREN { r }
  | u=UID { Regex.RegExVariable (Id.make u) }


base:
  | s=str { s }
  | DOT { "" }
  | BACKSLASH { "\\" }
  | SLASH { "/" }
  | HYPHEN { "-" }

(***** }}} *****)

(***** Examples {{{ *****)

examples:
  | LBRACE RBRACE
    { [] }
  | LBRACE exs=examples_inner RBRACE
    { exs }

examples_inner:
  | ex=example COMMA exs=examples_inner
    { ex::exs }
  | ex=example
    { [ex] }

example:
  | s1=str LEFTRIGHTARR s2=str
    { (s1,s2) }

str:
  | s=STR
    { undelimit_string s }

(***** }}} *****)
