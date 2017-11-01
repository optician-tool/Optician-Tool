typedef QUOTELESS_STRING = (UPPERCASE | LOWERCASE | DIGIT | " " | "'" | "_" | ":" | "/" | "-" | "." |  "=" | "+" | "[" | "]" | "(" | ")")*;;

typedef STRING_COMPONENT = UPPERCASE | LOWERCASE | DIGIT | "\"" | " " | "'" | "_" | ":" | "/" | "-" | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | "*" | ",";;
typedef STRING = STRING_COMPONENT*;;
typedef NONEMPTY_STRING = STRING_COMPONENT+;;
typedef DELIMITED_STRING = (UPPERCASE | LOWERCASE | DIGIT | "\\\"" | " " | "'" | "_" | ":" | "/" | "-" | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | "*" | ",")*;;
string_to_delimited = [STRING <=> DELIMITED_STRING {}]

typedef NO_STAR_STRING_COMPONENT = UPPERCASE | LOWERCASE | DIGIT | "\"" | " " | "'" | "_" | ":" | "/" | "-" | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" |  ",";;
typedef NO_STAR_DELIMITED_STRING_COMPONENT = UPPERCASE | LOWERCASE | DIGIT | "\\\"" | " " | "'" | "_" | ":" | "/" | "-" | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | ",";;
typedef STARLESS_STRING = NO_STAR_STRING_COMPONENT*;;
typedef STARLESS_DELIMITED_STRING = NO_STAR_DELIMITED_STRING_COMPONENT*;;

starless_string_to_delimited = [STARLESS_STRING <=> STARLESS_DELIMITED_STRING {}]

typedef COMMENT = "# " STRING;;
(*test COMMENT matches "# comment";;*)
typedef COMMENT_DICT = "{\"#comment\"=\"" DELIMITED_STRING "\"}";;
(*test COMMENT_DICT matches "{\"#comment\"=\"comment\"}";;*)

comment_map = [COMMENT <=> COMMENT_DICT {}]

typedef EMPTYDICT = "{}";;

typedef NON_WSP_CHAR = (LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | "+" | DIGIT | "," | "=" | "*" | "%");;
typedef ENV_VAR = (UPPERCASE | "_")+;;
typedef WORD = NON_WSP_CHAR+;;
(*test WORD matches "my_username";;*)

typedef SIMPLE_WORD = (LOWERCASE | UPPERCASE | DIGIT)+;;

typedef FOLDER = ( (WORD "/")* WORD (. | "/") )
		| ("${" ENV_VAR "}");;
(*test FOLDER matches "my_username";;*)
(*test FOLDER matches "${MY_HOME}";;*)

typedef MULTILINE_COMMENT = "/*" STARLESS_STRING ("\n" STARLESS_STRING)* "*/";;
(*test MULTILINE_COMMENT matches "/*test\nmultiline*/";;*)
(*test MULTILINE_COMMENT matches "/*testmultiline*/";;*)

typedef MULTILINE_COMMENT_DICT = "{\"#mcomment\"" (("{\"string\"=\""STARLESS_DELIMITED_STRING"\"}")+) "}";;
(*test MULTILINE_COMMENT_DICT matches "{\"#mcomment\"{\"string\"=\"test\"}{\"string\"=\"multiline\"}}";;*)
(*test MULTILINE_COMMENT_DICT matches "{\"#mcomment\"{\"string\"=\"testmultiline\"}}";;*)

multiline_comment_map = [MULTILINE_COMMENT <=> MULTILINE_COMMENT_DICT {}]