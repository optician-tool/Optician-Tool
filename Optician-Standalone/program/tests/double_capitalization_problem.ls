#use "base.decls"

typedef NAME = LOWERCASE (LOWERCASE)* ;;
typedef UPPERCASENAME = UPPERCASE (UPPERCASE)*;;

typedef LASTCOMMAFIRST = UPPERCASENAME ", " UPPERCASENAME ;;
typedef FIRSTTHENLAST = NAME " " NAME;;

capitalize = [LASTCOMMAFIRST <=> FIRSTTHENLAST
{}]
