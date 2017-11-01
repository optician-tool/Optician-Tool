#use "base.decls"
#use "util.decls"

typedef BRACKETLESS_STRING_COMPONENT =
  UPPERCASE | LOWERCASE | DIGIT | "\"" | " " | "'" | "_" | ":" | "/" | "-"
    | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | "*" | ",";;

typedef NONEMPTY_BRACKETLESS_STRING = BRACKETLESS_STRING_COMPONENT+;;

typedef BRACKETLESS_DELIMITED_STRING_COMPONENT =
  UPPERCASE | LOWERCASE | DIGIT | "\\\"" | " " | "'" | "_" | ":" | "/" | "-"
    | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | "*" | ",";;

typedef NONEMPTY_BRACKETLESS_DELIMITED_STRING = BRACKETLESS_STRING_COMPONENT+;;

typedef HASHLESS_STRING_COMPONENT =
  UPPERCASE | LOWERCASE | DIGIT | "\"" | " " | "'" | "_" | ":" | "/" | "-"
    | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | "*" | ",";;

typedef NONEMPTY_HASHLESS_STRING = HASHLESS_STRING_COMPONENT+;;

typedef HASHLESS_DELIMITED_STRING_COMPONENT =
  UPPERCASE | LOWERCASE | DIGIT | "\\\"" | " " | "'" | "_" | ":" | "/" | "-"
    | "." | "=" | "+" | "[" | "]" | "(" | ")" | ";" | "!" | "*" | ",";;

typedef NONEMPTY_HASHLESS_DELIMITED_STRING = BRACKETLESS_DELIMITED_STRING_COMPONENT+;;

typedef CARBON_ENTRY_ENTRY =
  WORD " =" ("" | (" " NONEMPTY_HASHLESS_STRING)) ("" | COMMENT);;
test CARBON_ENTRY_ENTRY matches "LINE_RECEIVER_INTERFACE = 0.0.0.0";;
test CARBON_ENTRY_ENTRY matches "MAX_CACHE_SIZE = inf # comment at EOL";;
test CARBON_ENTRY_ENTRY matches "USER =";;
test CARBON_ENTRY_ENTRY matches "USER =# test";;

typedef CARBON_ENTRY =
  ("[" NONEMPTY_BRACKETLESS_STRING "]\n")
  ((CARBON_ENTRY_ENTRY | COMMENT | "") "\n")*;;
test CARBON_ENTRY matches "[cache]
# Configure carbon directories.

# Specify the user to drop privileges to
# If this is blank carbon runs as the user that invokes it
# This user must have write access to the local data directory
USER =

MAX_CACHE_SIZE = inf # comment at EOL
LINE_RECEIVER_INTERFACE = 0.0.0.0
LINE_RECEIVER_PORT = 2003
ENABLE_UDP_LISTENER = False
";;

typedef CARBON_CONF = (CARBON_ENTRY)*;;
test CARBON_CONF matches
"[cache]
# Configure carbon directories.

# Specify the user to drop privileges to
# If this is blank carbon runs as the user that invokes it
# This user must have write access to the local data directory
USER =

MAX_CACHE_SIZE = inf # comment at EOL
LINE_RECEIVER_INTERFACE = 0.0.0.0
LINE_RECEIVER_PORT = 2003
ENABLE_UDP_LISTENER = False

[relay]
LINE_RECEIVER_INTERFACE = 0.0.0.0
LINE_RECEIVER_PORT = 2013
PICKLE_RECEIVER_INTERFACE = 0.0.0.0
PICKLE_RECEIVER_PORT = 2014
";;

typedef CARBON_ENTRY_ENTRY_DICT =
  "{\"" WORD "\""
    ("" | ("=\"" NONEMPTY_BRACKETLESS_DELIMITED_STRING "\""))
    ("" | COMMENT_DICT)
  "}" ;;

entry_entry_map = [CARBON_ENTRY_ENTRY <=> CARBON_ENTRY_ENTRY_DICT {}]

typedef CARBON_ENTRY_DICT =
  "{\"" NONEMPTY_BRACKETLESS_DELIMITED_STRING "\""
  (CARBON_ENTRY_ENTRY_DICT | "{ }" | COMMENT_DICT)* "}";;

entry_map = [CARBON_ENTRY <=> CARBON_ENTRY_DICT {}]

typedef CARBON_DICT = "" | ("{" CARBON_ENTRY_DICT+ "}");;

carbon_map = [CARBON_CONF <=> CARBON_DICT {}]
