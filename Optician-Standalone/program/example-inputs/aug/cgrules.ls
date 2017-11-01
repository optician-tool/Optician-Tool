#use "base.decls"
#use "util.decls"

typedef NON_WSP_NON_PERCENT_NON_AT_CHAR =
  (LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | "+" | DIGIT | "," | "=" | "*");;

typedef USERNAME = (NON_WSP_NON_PERCENT_NON_AT_CHAR)+;;

typedef GROUPNAME = "@"USERNAME;;

typedef USER_OR_GROUP_RECORD =
  (USERNAME | GROUPNAME) NONEMPTY_SAMELINE_WSP WORD NONEMPTY_SAMELINE_WSP WORD "\n"
  ("%" NONEMPTY_SAMELINE_WSP WORD NONEMPTY_SAMELINE_WSP WORD "\n")*;;

typedef USER_OR_GROUP_RECORD_DICT =
  "{\"" ("user" | "group") "\"=\"" USERNAME "\""
    ("{" NONEMPTY_SAMELINE_WSP "\"" WORD "\"=\"" WORD "\"" NONEMPTY_SAMELINE_WSP "}")+
  "}";;

user_or_group_record_map = [USER_OR_GROUP_RECORD <=> USER_OR_GROUP_RECORD_DICT {}]

typedef RULES_CONF =
  (USER_OR_GROUP_RECORD | (COMMENT "\n") | ("\n"))*;;

typedef RULES_DICT =
  "{" (USER_OR_GROUP_RECORD_DICT | COMMENT_DICT | "{ }")* "}";;

rules_map = [RULES_CONF <=> RULES_DICT {}]