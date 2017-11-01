#use "base.decls"
#use "util.decls"


typedef NO_COLON_WORD =
  (LOWERCASE | UPPERCASE | "_" | "." | "-" | "/" | "+" | "," | "=" | DIGIT)+;;

typedef NO_COLON_COMMA_EQ_WORD =
  (LOWERCASE | UPPERCASE | "_" | "." | "-" | "/" | "+" | DIGIT)+;;

typedef TYPE_HOST_FORMAT =
  ""
  | (NO_COLON_COMMA_EQ_WORD
      ("" | ("," NO_COLON_COMMA_EQ_WORD)) ":"
      (NO_COLON_COMMA_EQ_WORD ":" | ""));;

typedef OPTIONS =
  ""
  | ((
    NO_COLON_COMMA_EQ_WORD
    ("" | ("=" NO_COLON_COMMA_EQ_WORD)))
    (("," | NONEMPTY_SAMELINE_WSP)
    NO_COLON_COMMA_EQ_WORD
    ("" | ("=" NO_COLON_COMMA_EQ_WORD)))*);;

typedef AUTOMASTER =
  ((COMMENT
    | (WORD NONEMPTY_SAMELINE_WSP TYPE_HOST_FORMAT NO_COLON_WORD
      ("" | ((NONEMPTY_SAMELINE_WSP) OPTIONS)))
    | "")
  "\n")*;;

test AUTOMASTER matches
"# 
# Sample auto.master file
# 

/-        auto.data 
/net    -hosts ro
/misc   /etc/auto.misc
/home     /etc/auto.home
/home     ldap:example.com:ou=auto.home,dc=example,dc=com 
/mnt      yp:mnt.map -strict,-Dfoo=bar,uid=1000
/mnt      yp,sun:mnt.map
/auto   /etc/auto.HD --timeout=15 --ghost

+ dir:/etc/auto.master.d
+ auto.master
";;

typedef HOST_DICT =
  "{\"HOST\"=\"" NO_COLON_COMMA_EQ_WORD "\"}";;

typedef FORMAT_DICT =
  "{\"FORMAT\"=\"" NO_COLON_COMMA_EQ_WORD "\"}";;

typedef TYPE_HOST_FORMAT_DICTS =
  ""
  | (("{\"TYPE\"=\""
      (NO_COLON_COMMA_EQ_WORD)
      "\"}")
    ("" | HOST_DICT)
    ("" | FORMAT_DICT));;

typedef MAP_DICT =
  "{\"map\"=\"" NO_COLON_WORD "\"}";;

typedef VALUE_DICT = "{\"value\"=\"" NO_COLON_COMMA_EQ_WORD "\"}";;


typedef OPTIONS_DICT =
  ""
  | (("{\"opt\"=\"" NO_COLON_COMMA_EQ_WORD "\""
    ("" | VALUE_DICT))(("," | NONEMPTY_SAMELINE_WSP) "{\"opt\"=\"" NO_COLON_COMMA_EQ_WORD "\""
    ("" | VALUE_DICT))*);;

y = [OPTIONS_DICT <=> OPTIONS {}]

typedef AUTOMASTER_ENTRY_DICT =
  "{\"" WORD "\"" NONEMPTY_SAMELINE_WSP
    (TYPE_HOST_FORMAT_DICTS)
    (MAP_DICT)
    (""
    | (NONEMPTY_SAMELINE_WSP
    OPTIONS_DICT))
  "}";;

typedef AUTOMASTER_DICT =
  "{"
    (COMMENT_DICT | "{ }" | AUTOMASTER_ENTRY_DICT)*
  "}"
;;

automaster_to_dict = [ AUTOMASTER <=> AUTOMASTER_DICT {
"# 
# Sample auto.master file
# 

/-        auto.data 
/net    -hosts ro
/misc   /etc/auto.misc
/home     /etc/auto.home
/home     ldap:example.com:ou=auto.home,dc=example,dc=com 
/mnt      yp:mnt.map -strict,-Dfoo=bar,uid=1000
/mnt      yp,sun:mnt.map
/auto   /etc/auto.HD --timeout=15 --ghost

+ dir:/etc/auto.master.d
+ auto.master
"
<->
"{{\"#comment\"=\"\"}{\"#comment\"=\"Sample auto.master file\"}{\"#comment\"=\"\"}{ }{\"/-\"        {\"map\"=\"auto.data\"} }{\"/net\"    {\"map\"=\"-hosts\"} {\"opt\"=\"ro\"}{\"/misc\"   {\"map\"=\"/etc/auto.misc\"}}{\"/home\"     {\"map\"=\"/etc/auto.home\"}}{\"/home\"     {\"TYPE\"=\"ldap\"}{\"FORMAT\"=\"example.com\"}{\"map\"=\"ou=auto.home,dc=example,dc=com\"} }{\"/mnt\"      {\"TYPE\"=\"yp\"}{\"map\"=\"mnt.map\"} {\"opt\"=\"-strict\",{\"opt\"=\"-Dfoo\"{\"value\"=\"bar\"},{\"opt\"=\"uid\"{\"value\"=\"1000\"}}{\"/mnt\"      {\"TYPE\"=\"yp\"}{\"HOST\"=\"sun\"}{\"map\"=\"mnt.map\"}}{\"/auto\"   {\"map\"=\"/etc/auto.HD\"} {\"opt\"=\"--timeout\"{\"value\"=\"15\"} {\"opt\"=\"--ghost\"}{ }{\"+\" {\"TYPE\"=\"dir\"}{\"map\"=\"/etc/auto.master.d\"}}{\"+\" {\"map\"=\"auto.master\"}}}"
}]