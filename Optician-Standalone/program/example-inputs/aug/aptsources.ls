#use "base.decls"
#use "util.decls"

typedef OPERATION = "+" | "-";;

typedef OPTION_KVP_OPERATION_CONF = SIMPLE_WORD (OPERATION | .) "=" SIMPLE_WORD;;
test OPTION_KVP_OPERATION_CONF matches "arch+=amd64";;

typedef OPTIONS_DICT = "{\"options\"" ("{\""SIMPLE_WORD"\"=\""SIMPLE_WORD"\""(("{\"operation\"=\""OPERATION"\"}")|.)"}")+ "}";;
test OPTIONS_DICT matches "{\"options\"{\"arch\"=\"amd64\"{\"operation\"=\"+\"}}}";;

typedef OPTIONS_CONF = " [ " (OPTION_KVP_OPERATION_CONF " ")+ "] ";;
test OPTIONS_CONF matches " [ arch=amd64 trusted-=true ] ";;

typedef APTSOURCE_CONF = (WORD (" " | OPTIONS_CONF) WORD " " WORD (" " WORD)* "\n")*;;
test APTSOURCE_CONF matches "deb [ arch+=amd64 ] tor+http://ftp.us.debian.org/debian sid main contrib\n";;

typedef APTSOURCE_DICT = ("{\"type\"=\""WORD"\"}"(.|OPTIONS_DICT)"{\"uri\"=\""WORD"\"}{\"distribution\"=\""WORD"\"}" ("{\"component\"=\""WORD"\"}")*)*;;
test APTSOURCE_DICT matches "{\"type\"=\"deb\"}{\"options\"{\"arch\"=\"amd64\"{\"operation\"=\"+\"}}}{\"uri\"=\"tor+http://ftp.us.debian.org/debian\"}{\"distribution\"=\"sid\"}{\"component\"=\"main\"}{\"component\"=\"contrib\"}";;

aptsrc = [APTSOURCE_CONF <=> APTSOURCE_DICT {"deb [ arch+=amd64 ] tor+http://ftp.us.debian.org/debian sid main contrib\n" <-> "{\"type\"=\"deb\"}{\"options\"{\"arch\"=\"amd64\"{\"operation\"=\"+\"}}}{\"uri\"=\"tor+http://ftp.us.debian.org/debian\"}{\"distribution\"=\"sid\"}{\"component\"=\"main\"}{\"component\"=\"contrib\"}"}]
