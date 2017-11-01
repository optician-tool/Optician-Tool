#use "base.decls"
#use "util.decls"

typedef AUTHPAIR_RECORD_CONF = SIMPLE_WORD ": " SIMPLE_WORD ":" SIMPLE_WORD;;
test AUTHPAIR_RECORD_CONF matches "AdminAuth: mooma:moopa";;

typedef AUTHPAIR_RECORD_DICT = "{\""SIMPLE_WORD"\"{\""SIMPLE_WORD"\"=\""SIMPLE_WORD"\"}}";;
test AUTHPAIR_RECORD_DICT matches "{\"AdminAuth\"{\"mooma\"=\"moopa\"}}";;

typedef APTCACHERNGSECURITY_CONF = ((COMMENT | AUTHPAIR_RECORD_CONF | .) "\n")*;;
test APTCACHERNGSECURITY_CONF matches "# comment\nAdminAuth: mooma:moopa\n\n";;

typedef APTCACHERNGSECURITY_DICT = (COMMENT_DICT | AUTHPAIR_RECORD_DICT | EMPTYDICT)*;;
test APTCACHERNGSECURITY_DICT matches "{\"#comment\"=\"comment\"}{\"AdminAuth\"{\"mooma\"=\"moopa\"}}{}";;

apt_update_manager = [APTCACHERNGSECURITY_CONF <=> APTCACHERNGSECURITY_DICT {"# comment\nAdminAuth: mooma:moopa\n\n" <-> "{\"#comment\"=\"comment\"}{\"AdminAuth\"{\"mooma\"=\"moopa\"}}{}"}]
