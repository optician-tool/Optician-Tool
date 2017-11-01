#use "base.decls"
#use "util.decls"

typedef WS = (" " | "\t")+;;

typedef IPADDR = NUMBER "." NUMBER "." NUMBER "." NUMBER;;
typedef HOSTNAME = WORD;;
typedef HOSTSLINE = IPADDR WS HOSTNAME (WS HOSTNAME)* (WS COMMENT | .);;
typedef HOSTS = ((HOSTSLINE | . | COMMENT) "\n")*;;

typedef IPADDR_DICT = "{\"ipaddr\"=\"" IPADDR "\"}";;
typedef HOST_DICT = "{\"name\"=\"" HOSTNAME "\",\"ws\"=\"" WS "\"}";;
typedef COMM_DICT = "{\"comment\"=\"" COMMENT "\",\"ws\"=\"" WS "\"}";;
typedef HOSTLINE_DICT = "{\"ipaddrs\"=" IPADDR_DICT ",\"hosts\"=" HOST_DICT HOST_DICT* (COMM_DICT | .) "}";;
typedef HOSTS_DICT = ((HOSTLINE_DICT | EMPTYDICT | COMMENT_DICT) "\n")*;;

ipaddr_lens = [IPADDR <=> IPADDR_DICT {}]
hostline_lens = [HOSTSLINE <=> HOSTLINE_DICT {}]
hosts_lens = [HOSTS <=> HOSTS_DICT {}]

test hosts_lens { "127.0.0.1 localhost alias # comment\n" 
<-> 
"{\"ipaddrs\"={\"ipaddr\"=\"127.0.0.1\"},\"hosts\"={\"name\"=\"localhost\",\"ws\"=\" \"}{\"name\"=\"alias\",\"ws\"=\" \"}{\"comment\"=\"# comment\",\"ws\"=\" \"}}\n" };;
