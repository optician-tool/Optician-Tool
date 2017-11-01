#use "base.decls"
#use "util.decls"

typedef INDENT = (" " | "\t")*;;
typedef INDENT_REQ = (" " | "\t")+;;
typedef ALPHANUM = (UPPERCASE | LOWERCASE | DIGIT)+;;
typedef RANGE = (ALPHANUM "-" ALPHANUM | ALPHANUM );;
typedef PREFIX = "-";;

typedef SCHEDULE_VALUE = "reboot" | "yearly" | "annually" | "monthly"
                       | "weekly" | "daily" | "midnight" | "hourly";;
typedef SCHEDULE = "@" SCHEDULE_VALUE;;

typedef USER = (UPPERCASE | LOWERCASE | DIGIT)+;;

typedef TIME = NUMBER INDENT_REQ NUMBER INDENT_REQ NUMBER INDENT_REQ RANGE INDENT_REQ RANGE;;

typedef SHELLCOMMAND_CHAR = LOWERCASE | UPPERCASE | DIGIT | "_" | "/" | "|"  | "." ;;
typedef SC_CHAR_OR_SPACE = LOWERCASE | UPPERCASE | DIGIT | "_" | "/" | "|" | "." | " " ;;
typedef SHELLCOMMAND = (SHELLCOMMAND_CHAR (SC_CHAR_OR_SPACE)* SHELLCOMMAND_CHAR) | SHELLCOMMAND_CHAR;;

typedef SHELLVAR_CHAR = LOWERCASE | UPPERCASE | DIGIT | "_";; 
typedef SHELLVAR_NAME = SHELLVAR_CHAR+;;
typedef SHELLVALUE_CHAR = LOWERCASE | UPPERCASE | DIGIT | "_" | "/" | "|" | ".";;
typedef SHELLVALUE_NAME = SHELLVALUE_CHAR+;;

typedef SHELLVAR = SHELLVAR_NAME "=" SHELLVALUE_NAME "\n";;
typedef COMMENTLINE = COMMENT "\n";;
typedef ENTRY = INDENT (PREFIX | . ) (TIME | SCHEDULE) INDENT_REQ USER INDENT_REQ SHELLCOMMAND "\n";;
typedef CRON = ( "\n" | SHELLVAR | COMMENTLINE | ENTRY)*;;

typedef PREFIX_DICT = "{\"prefix\"=" ("true" | "false") "}";;
typedef TIME_DICT = "{\"minute\"=" NUMBER ",\"ws1\"=" INDENT_REQ ",\"hour\"=" NUMBER 
  ",\"ws2\"=" INDENT_REQ ",\"dayofmonth\"=" NUMBER ",\"ws3\"=" INDENT_REQ 
  ",\"month\"=" RANGE ",\"ws4\"=" INDENT_REQ ",\"dayofweek\"=" RANGE "}";;
typedef SCHEDULE_DICT = "{\"schedule\"=\"" SCHEDULE_VALUE "\"}";;
typedef ENTRY_DICT = "{\"indent\"=\"" INDENT "\"," PREFIX_DICT "," (TIME_DICT | SCHEDULE_DICT)
  ",\"indent2\"=\"" INDENT_REQ "\",\"user\"=\"" USER "\",\"indent3\"=\""
  INDENT_REQ "\",\"command\"=\"" SHELLCOMMAND "\"}";;
typedef SHELL_DICT = "{\"varname\"=\"" SHELLVAR_NAME "\",\"value\"=\"" SHELLVALUE_NAME "\"}";;
typedef CRON_DICT = ((EMPTYDICT | SHELL_DICT | COMMENT_DICT | ENTRY_DICT) "\n")*;;

cron_lens = [CRON_DICT <=> CRON {}]
