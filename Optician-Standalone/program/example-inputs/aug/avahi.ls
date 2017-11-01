#use "base.decls"
#use "util.decls"

typedef TITLE = "[" STRING "]";;
typedef NO_EQUALS_WORD = (LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | "+" | DIGIT | "," | "*")+;;
typedef KVP = NO_EQUALS_WORD "=" NO_EQUALS_WORD;;
typedef TITLED_INFO = TITLE "\n" (KVP "\n")*;;

typedef AVAHI = (TITLED_INFO | "\n")*;;
test AVAHI matches "
[server]
host-name=web
domain=example.com

[wide-area]
enable-wide-area=yes
";;

typedef KVP_DICT = "{\"" NO_EQUALS_WORD "\"=\"" NO_EQUALS_WORD "\"}";;
typedef TITLED_KVP_DICT = "{\"" DELIMITED_STRING "\"" KVP_DICT* "}";;

typedef AVAHI_DICT = "{" ("{ }" | TITLED_KVP_DICT)* "}";;

avahi_map = [AVAHI <=> AVAHI_DICT
{
"
[server]
host-name=web
domain=example.com

[wide-area]
enable-wide-area=yes
"
<->
"{{ }{\"server\"{\"host-name\"=\"web\"}{\"domain\"=\"example.com\"}}{ }{\"wide-area\"{\"enable-wide-area\"=\"yes\"}}}"
}]