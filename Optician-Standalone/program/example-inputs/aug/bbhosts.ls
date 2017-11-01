#use "base.decls"
#use "util.decls"

typedef NON_WSP_START_NONEMPTY_STRING = NON_WSP_CHAR STRING;;
typedef NON_WSP_START_NONEMPTY_DELIMITED_STRING = NON_WSP_CHAR DELIMITED_STRING;;

typedef PAGE_TITLE = "page " SIMPLE_WORD " " STRING;;
test PAGE_TITLE matches "page firstpage My first page";;

typedef GROUP_INFO =
  ("group-compress" NONEMPTY_SAMELINE_WSP NON_WSP_START_NONEMPTY_STRING)
  | ("group-only"
      NONEMPTY_SAMELINE_WSP SIMPLE_WORD NONEMPTY_SAMELINE_WSP NON_WSP_START_NONEMPTY_STRING);;

typedef IP_NUMBER = (DIGIT | DIGIT DIGIT | DIGIT DIGIT DIGIT);;

typedef IP_ADDRESS = IP_NUMBER "." IP_NUMBER "." IP_NUMBER "." IP_NUMBER;;
test IP_ADDRESS matches "1.2.3.4";;

typedef URL = ("http" | "https") WORD;;
test URL matches "http://url.to/monitor";;

typedef PROBE_TYPE =
  "cont" | "noping" | "noconn" | "ssh" | "dns" | "pop3" | "imap2"
    | "telnet" | "fping" | "http" | "ftps" | "imaps" | "imap4"
    | "pop-3" | "pop2s" | "pop" | "smtp" | "smtps" | "ssh1" | "ssh2"
    | "telnets";;

typedef PROBE = (("!" | "") PROBE_TYPE) | URL;;

typedef PROBE_DICT =
  ("{\"" PROBE_TYPE "\"=\"" ("!" | "") "\"")
    | ("{\"url\"=\"" URL "\"");;
probe_map = [PROBE <=> PROBE_DICT {}]

typedef PROBE_WITH_SUBSTUFF =
  PROBE ("" | (";" WORD) | (";" WORD ";" WORD));;
test PROBE_WITH_SUBSTUFF matches "http://url.to/monitor";;
test PROBE_WITH_SUBSTUFF matches "https://another.url/to/monitor";;
test PROBE_WITH_SUBSTUFF matches "cont;http://a.cont.url/to/monitor;wordtofind";;

typedef PROBE_WITH_SUBSTUFF_DICT =
  PROBE_DICT
    (""
      | (("{\"url\"=\"" WORD "\"}")
          (""
            | "{\"keyword\"=\"" WORD "\"}"))) "}";;

probe_with_substuff_map = [PROBE_WITH_SUBSTUFF <=> PROBE_WITH_SUBSTUFF_DICT {}]

typedef DATETIME = NUMBER | "*";;

typedef DOWNTIME =
  "DOWNTIME=" ("" | (PROBE_TYPE ("," PROBE_TYPE)*))
    (":" DATETIME)
    (":" DATETIME)
    (":" DATETIME)
    (":" "\"" QUOTELESS_STRING "\"");;
test DOWNTIME matches "DOWNTIME=fping,http:*:1800:1015:\"Frontal 01 Redirect Amazon eteint entre 18h et 10h\"";;

typedef DOWNTIME_DICT =
  "{\"DOWNTIME\""
    ("{\"probe\"=\"" PROBE_TYPE "\"}")*
    "{\"day\"=\"" DATETIME "\"}"
    "{\"starttime\"=\"" DATETIME "\"}"
    "{\"endtime\"=\"" DATETIME "\"}"
    "{\"cause\"=\"" QUOTELESS_STRING "\"}"
  "}";;

typedef PROBES =
  "#" (NONEMPTY_SAMELINE_WSP (PROBE_WITH_SUBSTUFF | DOWNTIME))*;;
test PROBES matches "# http://url.to/monitor https://another.url/to/monitor cont;http://a.cont.url/to/monitor;wordtofind";;

typedef PROBES_DICT =
  ""
  | ("{\"probes\""
    (NONEMPTY_SAMELINE_WSP (PROBE_WITH_SUBSTUFF_DICT | DOWNTIME_DICT))+
    "}");;


typedef USER_ADDR = IP_ADDRESS NONEMPTY_SAMELINE_WSP WORD NONEMPTY_SAMELINE_WSP PROBES;;
test USER_ADDR matches "1.2.3.4		amachine	# http://url.to/monitor https://another.url/to/monitor cont;http://a.cont.url/to/monitor;wordtofind";;
test USER_ADDR matches "1.2.3.5		amachine2	# http://url.to/monitor https://another.url/to/monitor !cont;http://a.cont.url/to/monitor;wordtofind";;

typedef GROUP = GROUP_INFO "\n" ((USER_ADDR | COMMENT | "") "\n")*;;
test GROUP matches "group-compress  A group
1.2.3.4		amachine	# http://url.to/monitor https://another.url/to/monitor cont;http://a.cont.url/to/monitor;wordtofind
1.2.3.5		amachine2	# http://url.to/monitor https://another.url/to/monitor !cont;http://a.cont.url/to/monitor;wordtofind
# a comment in a group


";;

typedef PAGE = PAGE_TITLE "\n" (("" | COMMENT) "\n")* GROUP*;;
test PAGE matches "page firstpage My first page

# page comment


group-compress  A group
1.2.3.4		amachine	# http://url.to/monitor https://another.url/to/monitor cont;http://a.cont.url/to/monitor;wordtofind
1.2.3.5		amachine2	# http://url.to/monitor https://another.url/to/monitor !cont;http://a.cont.url/to/monitor;wordtofind
# a comment in a group


group-only  dns VIP DNS
10.50.25.48	mydnsmachine.network #
10.50.25.49     myotherdnsmachine.network # noping noconn !ssh dns;mydnstocheck
# a comment in a group
";;

typedef CONF = (("" | COMMENT) "\n")* PAGE*;;
test CONF matches "
# A comment

page firstpage My first page

group-compress  A group
1.2.3.4		amachine	# http://url.to/monitor https://another.url/to/monitor cont;http://a.cont.url/to/monitor;wordtofind
1.2.3.5		amachine2	# http://url.to/monitor https://another.url/to/monitor !cont;http://a.cont.url/to/monitor;wordtofind

group-only  dns  VIP DNS
10.50.25.48	mydnsmachine.network #
10.50.25.49     myotherdnsmachine.network # noping noconn !ssh dns;mydnstocheck
# a comment in a group


page anotherpage A new page

# a comment in a page

group-compress My test
192.168.0.2	myhost	# https://myurl.com:1256 noconn pop3 imap2 ssh
192.168.0.3	myhost2 # !imap2 telnet dns

group-compress DownTime
0.0.0.0	myhost3 # DOWNTIME=fping,http:*:1800:1015:\"Frontal 01 Redirect Amazon eteint entre 18h et 10h\"
0.0.0.0	myhost4 # ftps imaps imap4 pop-3 pop2s pop smtp smtps ssh ssh1 ssh2 telnet telnets
";;

typedef USER_ADDR = IP_ADDRESS NONEMPTY_SAMELINE_WSP WORD NONEMPTY_SAMELINE_WSP PROBES;;
test USER_ADDR matches "1.2.3.4		amachine	# http://url.to/monitor https://another.url/to/monitor cont;http://a.cont.url/to/monitor;wordtofind";;
test USER_ADDR matches "1.2.3.5		amachine2	# http://url.to/monitor https://another.url/to/monitor !cont;http://a.cont.url/to/monitor;wordtofind";;

typedef GROUP = GROUP_INFO "\n" ((USER_ADDR | COMMENT | "") "\n")*;;

typedef GROUP_DICT =
  (("{\"group-compress\"=\"" NON_WSP_START_NONEMPTY_DELIMITED_STRING "\"" NONEMPTY_SAMELINE_WSP)
    | ("{\"group-only\"=\"" NON_WSP_START_NONEMPTY_DELIMITED_STRING "\"" NONEMPTY_SAMELINE_WSP
        "{\"col\"=\"" SIMPLE_WORD "\"}" NONEMPTY_SAMELINE_WSP))
  (("{\"host\"{\"ip\"=\"" IP_ADDRESS "\"}" NONEMPTY_SAMELINE_WSP
      "{\"fqdn\"=\"" WORD "\"}" NONEMPTY_SAMELINE_WSP PROBES_DICT)
    | COMMENT_DICT | "{ }")* "}";;


typedef PAGE_DICT =
  "{\"page\"=\"" SIMPLE_WORD "\"" "{\"title\"=\"" DELIMITED_STRING "\"}"
  ("{ }" | COMMENT_DICT)*
  (GROUP_DICT)*
  "}";;

typedef DICT = ("{ }" | COMMENT_DICT)* PAGE_DICT*;;

map = [CONF <=> DICT {}]