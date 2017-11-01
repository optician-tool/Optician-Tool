#use "base.decls"
#use "util.decls"

typedef COMMA_SEPARATED_NONEMPTY_WORD_LIST = (SIMPLE_WORD ",")*SIMPLE_WORD;;
typedef NAME_VALUE_CONF = SIMPLE_WORD":"COMMA_SEPARATED_NONEMPTY_WORD_LIST;;
typedef ALIASCONF = ((NAME_VALUE_CONF | . | COMMENT) "\n")*;;

typedef VALUE_DICT = "{\"value\"=\""SIMPLE_WORD"\"}";;
typedef NAME_VALUE_DICT = "{\"name\"=\""SIMPLE_WORD"\""VALUE_DICT+"}";;
typedef ALIAS_DICT = (NAME_VALUE_DICT | EMPTYDICT | COMMENT_DICT)*;;

afs_cellalias = [ALIAS_DICT <=> ALIASCONF {}]
