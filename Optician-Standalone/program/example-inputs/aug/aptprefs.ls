#use "base.decls"
#use "util.decls"

typedef EXPLANATION_CONF = "Explanation: " STRING;;
test EXPLANATION_CONF matches "Explanation: Backport packages are never prioritary";;

typedef EXPLANATION_DICT = "{\"Explanation\"=\""STRING"\"}";;
test EXPLANATION_DICT matches "{\"Explanation\"=\"Backport packages are never prioritary\"}";;


typedef PACKAGE_CONF = "Package: " (STRING);;
test PACKAGE_CONF matches "Package: *";;

typedef PACKAGE_DICT = "{\"Package\"=\"" (STRING) "\"}";;
test PACKAGE_DICT matches "{\"Package\"=\"*\"}";;


typedef PIN_CONF = "Pin: " STRING;;
test PIN_CONF matches "Pin: release a=backports";;
typedef PIN_DICT = "{\"Pin\"=\"" STRING "\"}";;
test PIN_DICT matches "{\"Pin\"=\"release a=backports\"}";;

typedef PIN_PRIORITY_CONF = "Pin-Priority: " NUMBER;;
test PIN_PRIORITY_CONF matches "Pin-Priority: 700";;

typedef PIN_PRIORITY_DICT = "{\"Pin-Priority\"=\"" NUMBER "\"}";;
test PIN_PRIORITY_DICT matches "{\"Pin-Priority\"=\"700\"}";;


typedef OPTION_CONF = ((EXPLANATION_CONF | PACKAGE_CONF | PIN_CONF | PIN_PRIORITY_CONF | COMMENT) "\n");;

typedef APTPREFS_CONF = (OPTION_CONF (("\n" OPTION_CONF)*));;
typedef APTPREFS_DICT = ("{\"Pref\"=" (EXPLANATION_DICT | PACKAGE_DICT | PIN_DICT | PIN_PRIORITY_DICT | COMMENT_DICT)"}")+;;

x = [APTPREFS_CONF <=> APTPREFS_DICT {(*"Explanation: Backport packages are never prioritary\nPackage: *\nPin: release a=backports\nPin-Priority: 700\n" <-> "{\"Pref\"={\"Explanation\"=\"Backport packages are never prioritary\"}{\"Package\"=\"*\"}{\"Pin\"=\"release a=backports\"}{\"Pin-Priority\"=\"700\"}}"*)}]

