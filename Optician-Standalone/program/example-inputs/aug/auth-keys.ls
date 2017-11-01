#use "base.decls"
#use "util.decls"

typedef OPTION_KEY = "command" | "environment" | "from" | "permitopen" | "principals" | "tunnel";;

typedef FLAG = "cert-authority" | "no-agent-forwarding" | "no-port-forwarding" | "no-pty" | "no-user-rc" | "no-X11-forwarding";;

typedef KEY = (UPPERCASE | LOWERCASE | DIGIT | "+" | "/")+;;

typedef KEY_TYPE = ("ssh-"((LOWERCASE | DIGIT)+))|("ecdsa-sha2-nistp"(DIGIT+));;

typedef OPTION_KVP_DICT = "{\""OPTION_KEY"\"=\""STRING"\"}";;
typedef OPTION_FLAG_DICT = "{\""FLAG"\"}";;
typedef OPTION_DICT = . | ("{\"options\"" (OPTION_KVP_DICT | OPTION_FLAG_DICT)+ "}");;

typedef OPTION_ELEMENT_CONF = ((OPTION_KEY "=\"" DELIMITED_STRING "\"") | FLAG);;

typedef OPTION_LIST_CONF = (. | (OPTION_ELEMENT_CONF (("," OPTION_ELEMENT_CONF)*) " "));;

typedef KEY_CONF = OPTION_LIST_CONF KEY_TYPE " " KEY (. | (" " NONEMPTY_STRING));;
test KEY_CONF matches "cert-authority,command=\"t\" ssh-dsa 12345 my comment";;

typedef KEY_DICT = "{\"key\"=\"" KEY "\"" OPTION_DICT "{\"type\"=\""KEY_TYPE"\"}" (. | ("{\"comment\"=\""NONEMPTY_STRING"\"}"))"}";;
test KEY_DICT matches "{\"key\"=\"12345\"{\"options\"{\"cert-authority\"}{\"command\"=\"t\"}}{\"type\"=\"ssh-dsa\"}{\"comment\"=\"my comment\"}}";;

x = [KEY_CONF <=> KEY_DICT {"cert-authority,command=\"t\" ssh-dsa 12345 my comment"<->"{\"key\"=\"12345\"{\"options\"{\"cert-authority\"}{\"command\"=\"t\"}}{\"type\"=\"ssh-dsa\"}{\"comment\"=\"my comment\"}}"}]
