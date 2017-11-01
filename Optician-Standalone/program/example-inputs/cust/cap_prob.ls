#use "base.decls"

typedef NAME = UPPERCASE (LOWERCASE)* ;;
typedef UPPERCASENAME = UPPERCASE (UPPERCASE)*;;

capitalize = [UPPERCASENAME <=> NAME
{"DOE" <-> "Doe"}]

test capitalize
{
"JOHN" <-> "John",
"DOE" <-> "Doe"
};;