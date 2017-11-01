#use "base.decls"

typedef NAME = UPPERCASE (LOWERCASE)* ;;
typedef UPPERCASENAME = UPPERCASE (UPPERCASE)*;;

capitalize = [UPPERCASENAME <=> NAME
{"MILTNER" <-> "Miltner"}]

test capitalize
{
"ANDERS" <-> "Anders",
"TESTER" <-> "Tester"
};;