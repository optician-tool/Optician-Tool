#use "base.decls"
#use "util.decls"

typedef SAMELINE_NON_SEMI_QUOTELESS_CHAR =
  (LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | "+" | DIGIT | "," |
  "=" | "*" | " " | "\t");;

typedef SAMELINE_NON_COLON_AT_QUOTELESS_PLUSLESS_CHAR =
  (LOWERCASE | UPPERCASE | "_" | "." | "-" | ";" | "/" | DIGIT | "," |
  "=" | "*" | " " | "\t");;

typedef ENTRY_NAME = SAMELINE_NON_SEMI_QUOTELESS_CHAR+;;

typedef VALUE = SAMELINE_NON_COLON_AT_QUOTELESS_PLUSLESS_CHAR+;;

typedef LANG = (UPPERCASE | LOWERCASE | DIGIT)+;;

typedef ENTRY_CONF =
  ENTRY_NAME
  ";" VALUE
  ":" NUMBER
  ":" VALUE
  ":" VALUE
  ":" NUMBER
  ":" NUMBER "=" NUMBER
  ((":" NUMBER "=" ("" | LANG ("+" LANG)* )) "@" NUMBER)*
  ":" NUMBER
  ":" NUMBER
  ":" NUMBER
  ":" NUMBER
  ":" NUMBER
  ":" NUMBER;;
test ENTRY_CONF matches "Direct 8 TV;SES ASTRA:12551:VC56M2O0S0:S19.2E:22000:1111=2:1112=fra@3:1116:0:12174:1:1108:0";;

typedef ENTRY_DICT =
  "{\"entry\"=\"" ENTRY_NAME "\""
    "{\"provider\"=\"" VALUE "\"}"
    "{\"frequency\"=\"" NUMBER "\"}"
    "{\"parameter\"=\"" VALUE "\"}"
    "{\"signal_source\"=\"" VALUE "\"}"
    "{\"symbol_rate\"=\"" NUMBER "\"}"
    "{\"tpid\"=\"" NUMBER "\"}"
    "{\"caid\"=\"" NUMBER "\"}"
    "{\"sid\"=\"" NUMBER "\"}"
    "{\"nid\"=\"" NUMBER "\"}"
    "{\"tid\"=\"" NUMBER "\"}"
    "{\"rid\"=\"" NUMBER "\"}"
    "{\"vpid\"=\"" NUMBER "\"" "{\"codec\"=\"" NUMBER "\"}}"
    ("{\"apid\"=\"" NUMBER "\"" ("{\"lang\"=\"" LANG "\"}")* "{\"codec\"=\"" NUMBER "\"}}")*
  "}";;

typedef THIS_COMMENT = "; " STRING;;

entry_map = [ENTRY_CONF <=> ENTRY_DICT
{
"Direct 8 TV;SES ASTRA:12551:VC56M2O0S0:S19.2E:22000:1111=2:1112=fra@3:1116:0:12174:1:1108:0"
<->
"{\"entry\"=\"Direct 8 TV\"{\"provider\"=\"SES ASTRA\"}{\"frequency\"=\"12551\"}{\"parameter\"=\"VC56M2O0S0\"}{\"signal_source\"=\"S19.2E\"}{\"symbol_rate\"=\"22000\"}{\"tpid\"=\"1116\"}{\"caid\"=\"0\"}{\"sid\"=\"12174\"}{\"nid\"=\"1\"}{\"tid\"=\"1108\"}{\"rid\"=\"0\"}{\"vpid\"=\"1111\"{\"codec\"=\"2\"}}{\"apid\"=\"1112\"{\"lang\"=\"fra\"}{\"codec\"=\"3\"}}}"
}]

typedef CHANNELS_CONF =
  ((ENTRY_CONF | THIS_COMMENT) "\n")*
  (":" ENTRY_NAME "\n" ((ENTRY_CONF | THIS_COMMENT) "\n")*)*;;

typedef CHANNELS_DICT =
  "{"
    (ENTRY_DICT | COMMENT_DICT)*
    ("{\"group\"=\"" ENTRY_NAME "\"" (ENTRY_DICT | COMMENT_DICT)* "}")*
  "}";;

channels_map = [CHANNELS_CONF <=> CHANNELS_DICT
{
"Direct 8 TV;SES ASTRA:12551:VC56M2O0S0:S19.2E:22000:1111=2:1112=fra@3:1116:0:12174:1:1108:0\n"
<->
"{{\"entry\"=\"Direct 8 TV\"{\"provider\"=\"SES ASTRA\"}{\"frequency\"=\"12551\"}{\"parameter\"=\"VC56M2O0S0\"}{\"signal_source\"=\"S19.2E\"}{\"symbol_rate\"=\"22000\"}{\"tpid\"=\"1116\"}{\"caid\"=\"0\"}{\"sid\"=\"12174\"}{\"nid\"=\"1\"}{\"tid\"=\"1108\"}{\"rid\"=\"0\"}{\"vpid\"=\"1111\"{\"codec\"=\"2\"}}{\"apid\"=\"1112\"{\"lang\"=\"fra\"}{\"codec\"=\"3\"}}}}"
}]