#use "base.decls"
#use "util.decls"

typedef ENV_VAR_CONF = ENV_VAR " = " STRING;;

typedef RELEASE_NAME = (UPPERCASE)+;;

typedef RELEASE_TITLE_CONF = "["RELEASE_NAME"]";;

typedef RELEASE_CONF = RELEASE_TITLE_CONF ("\n" ENV_VAR_CONF)*;;
test RELEASE_CONF matches "[DEFAULT]\nURI = http://changelogs.ubuntu.com/meta-release";;

typedef ENV_VAR_DICT = "{\""ENV_VAR"\"=\""DELIMITED_STRING"\"}";;

typedef RELEASE_DICT = "{\""RELEASE_NAME"\"="ENV_VAR_DICT*"}";;
test RELEASE_DICT matches "{\"DEFAULT\"={\"URI\"=\"http://changelogs.ubuntu.com/meta-release\"}}";;

typedef APT_UPDATE_CONF = ((COMMENT | RELEASE_CONF | .) "\n")*;;
test APT_UPDATE_CONF matches "# comment\n[DEFAULT]\nURI = http://changelogs.ubuntu.com/meta-release\n\n";;

typedef APT_UPDATE_DICT = (COMMENT_DICT | RELEASE_DICT | EMPTYDICT)*;;
test APT_UPDATE_DICT matches "{\"#comment\"=\"comment\"}{\"DEFAULT\"={\"URI\"=\"http://changelogs.ubuntu.com/meta-release\"}}{}";;

apt_update_manager = [APT_UPDATE_CONF <=> APT_UPDATE_DICT {"# comment\n[DEFAULT]\nURI = http://changelogs.ubuntu.com/meta-release\n\n" <-> "{\"#comment\"=\"comment\"}{\"DEFAULT\"={\"URI\"=\"http://changelogs.ubuntu.com/meta-release\"}}{}"}]
