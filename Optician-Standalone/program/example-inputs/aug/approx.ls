#use "base.decls"
#use "util.decls"

typedef VARIABLE = "$" WORD;;
test VARIABLE matches "$test-ing";;

typedef VARIABLE_VALUE_CONF = VARIABLE "	" STRING;;
test VARIABLE_VALUE_CONF matches "$test-ing	test val";;

typedef APPROX_CONF = ((VARIABLE_VALUE_CONF | COMMENT | .) "\n")*;;

typedef VARIABLE_VALUE_DICT = "{\""VARIABLE"\"=\""STRING"\"}";;
test VARIABLE_VALUE_DICT matches "{\"$test-ing\"=\"test val\"}";;

typedef APPROX_DICT = (VARIABLE_VALUE_DICT | COMMENT_DICT | EMPTYDICT)*;;

afs_cellalias = [APPROX_CONF <=> APPROX_DICT {
"# comment

$test-ing	test val
" <->
"{\"#comment\"=\"comment\"}{}{\"$test-ing\"=\"test val\"}"}]
