#use "base.decls"
#use "util.decls"


typedef ACCESSTYPE = "+" | "-";;


typedef COMMENT_KVP = "\"#comment\"=\"" DELIMITED_STRING "\"";;
typedef ORIGIN = (UPPERCASE | LOWERCASE | DIGIT | ":")+;;
typedef ORIGIN_KV = "{ \"origin\" = \"" ORIGIN "\" }";;
typedef ORIGIN_DICT = ("\n" ORIGIN_KV)*;;
typedef ORIGINLIST = (" " ORIGIN)*;;
typedef IDENTIFIER = (UPPERCASE | LOWERCASE | DIGIT)(UPPERCASE | LOWERCASE | DIGIT)*;;
typedef USERNAMEHOSTGROUPCONFIG = IDENTIFIER | (IDENTIFIER "@" IDENTIFIER) | ("@" IDENTIFIER);;
typedef USERNAMEHOSTGROUPCONFIGLIST = (USERNAMEHOSTGROUPCONFIG " ")*;;
typedef USERINFO = "{ \"user\" = \"" IDENTIFIER "\" }";;
typedef USERHOSTINFO = "{ \"user\" = \"" IDENTIFIER "\"\n	{ \"host\" = \"" IDENTIFIER "\" } }";;
typedef NETGROUPINFO = "{ \"netgroup\" = \"" IDENTIFIER "\" }";;
typedef UNHGCFG_KVP = USERINFO | USERHOSTINFO | NETGROUPINFO;;
typedef UNHGCFG_KVPLIST = ("\n" UNHGCFG_KVP)*;;

typedef CONFIG_COMMENT = "# " STRING;;


typedef FULLCONFIGACCESS = ACCESSTYPE " : " USERNAMEHOSTGROUPCONFIGLIST ":" ORIGINLIST;;
typedef FULL_ACCESS_CONFIG = ((FULLCONFIGACCESS | CONFIG_COMMENT) "\n")*;;

typedef CONFIGACCESSDICT = ("{ \"access\" = \"" ACCESSTYPE "\"" UNHGCFG_KVPLIST ORIGIN_DICT " }");;
typedef FULL_ACCESS_DICT = ((CONFIGACCESSDICT | COMMENT_KVP) "\n")*;;


typedef CONFIG_STRING = (CONFIG_COMMENT "\n")*;;

extract_netgroup = [("@" IDENTIFIER) <=> NETGROUPINFO
{
"@domain" <-> "{ \"netgroup\" = \"domain\" }"
}]

extract_origin_list = [ORIGINLIST <=> ORIGIN_DICT
{" cron crond :0" <-> "\n{ \"origin\" = \"cron\" }\n{ \"origin\" = \"crond\" }\n{ \"origin\" = \":0\" }"}]

extract_userdata = [USERNAMEHOSTGROUPCONFIG <=> UNHGCFG_KVP
{"john" <-> "{ \"user\" = \"john\" }",
"john@domain" <-> "{ \"user\" = \"john\"\n	{ \"host\" = \"domain\" } }",
"@domain" <-> "{ \"netgroup\" = \"domain\" }"
}]

extract_access = [FULLCONFIGACCESS <=> CONFIGACCESSDICT
{"+ : john john@domain @domain : cron crond :0" <-> "{ \"access\" = \"+\"\n{ \"user\" = \"john\" }\n{ \"user\" = \"john\"\n	{ \"host\" = \"domain\" } }\n{ \"netgroup\" = \"domain\" }\n{ \"origin\" = \"cron\" }\n{ \"origin\" = \"crond\" }\n{ \"origin\" = \":0\" } }"}]

extract_config = [FULL_ACCESS_CONFIG <=> FULL_ACCESS_DICT
{"+ : john john@domain @domain : cron crond :0\n# here is a comment with \"quotes\"\n" <-> "{ \"access\" = \"+\"\n{ \"user\" = \"john\" }\n{ \"user\" = \"john\"\n	{ \"host\" = \"domain\" } }\n{ \"netgroup\" = \"domain\" }\n{ \"origin\" = \"cron\" }\n{ \"origin\" = \"crond\" }\n{ \"origin\" = \":0\" } }\n\"#comment\"=\"here is a comment with \\\"quotes\\\"\"\n"}]
