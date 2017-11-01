#use "base.decls"

typedef NAME = UPPERCASE (LOWERCASE)* ;;

typedef NUMBER = DIGIT (DIGIT)* ;;

typedef STREETTYPE = "Road" | "Avenue" | "Street" | "Boulevard""" ;;

typedef CARDINALDIRECTION = "North" | "South" | "East" | "West" ;;

typedef STREETNAME = NAME (" " NAME)* ((" " STREETTYPE) | .)
			(. | (" " CARDINALDIRECTION)) ;;

typedef ZIP = DIGIT DIGIT DIGIT DIGIT DIGIT ;;

typedef STATE = UPPERCASE UPPERCASE ;;

typedef CSV_ADDRESS = (NAME "," NAME ","
	STATE "," ZIP "," NAME "," NUMBER "," STREETNAME "\n") ;;

typedef LETTER_ADDRESS = (NAME " " NAME "\n" NUMBER " " STREETNAME "\n"
			(UPPERCASE (LOWERCASE)*) ", " STATE " " " " ZIP) ;;

typedef CSV_ADDRESS_DATABASE = CSV_ADDRESS*;;
typedef LETTER_ADDRESS_LIST = . | (LETTER_ADDRESS  ("\n\n" LETTER_ADDRESS)*);;

csv_to_letter = [CSV_ADDRESS_DATABASE <=> LETTER_ADDRESS_LIST
{"Doe,John,NP,12345,Porttown,88,Town Road West
Doe,Jane,CJ,54321,Greentown,610,Direction House
" <-> 
"John Doe
88 Town Road West
Porttown, NP  12345

Jane Doe
610 Direction House
Greentown, CJ  54321"}]

test csv_to_letter
{"Doe,John,NP,12345,Porttown,88,Town Road West
Doe,Jane,CJ,54321,Greentown,610,Direction House
" <-> 
"John Doe
88 Town Road West
Porttown, NP  12345

Jane Doe
610 Direction House
Greentown, CJ  54321",
"" <-> "",
"Doe,John,MI,98765,Cityyy,1620,Rosey Avenue
" <->
"John Doe
1620 Rosey Avenue
Cityyy, MI  98765"};;
