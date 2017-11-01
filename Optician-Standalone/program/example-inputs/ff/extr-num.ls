#use "base.decls"
#use "util.decls"

typedef PHONENUMBER = DIGIT DIGIT DIGIT "-" DIGIT DIGIT DIGIT "-" DIGIT DIGIT DIGIT DIGIT ;;
test PHONENUMBER matches "415-342-3622";;
typedef PHONENUMBERHIDDEN = TEXT PHONENUMBER TEXT;;
test PHONENUMBERHIDDEN matches "asdfscxv as df415-342-3622 asdfasdf v a";;
typedef PHONENUMBEREXPLICIT = "number: \"" PHONENUMBER "\"\nbeforetext: \"" TEXT "\"\naftertext: \"" TEXT "\"";;
test PHONENUMBEREXPLICIT matches "number: \"415-342-3622\"\nbeforetext: \"asdfscxv as df\"\naftertext: \" asdfasdf v a\"";;

extract_number = [PHONENUMBERHIDDEN <=> PHONENUMBEREXPLICIT
{
"asdfscxv as df415-342-3622 asdfasdf v a"
<->
"number: \"415-342-3622\"\nbeforetext: \"asdfscxv as df\"\naftertext: \" asdfasdf v a\""
}]
