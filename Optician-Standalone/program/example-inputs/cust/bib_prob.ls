#use "base.decls"
typedef NAME = UPPERCASE (LOWERCASE)*;;

typedef LASTCOMMASTART = NAME "," (WSP NAME)*;;

typedef STARTTOEND = (NAME WSP)* NAME;;

typedef BIBTEXAUTHORLIST = LASTCOMMASTART (" and " LASTCOMMASTART)*;;
typedef BIBTEXAUTHORINFO = "author={" BIBTEXAUTHORLIST "}";;

typedef AUTAG = "au - ";;
typedef TITAG = "ti - ";;
typedef JOTAG = "jo - ";;

typedef TAGGEDAUTHORDEFNS = AUTAG STARTTOEND ("\n " AUTAG STARTTOEND)*;;

typedef TITLE = NAME (WSP NAME)*;;
typedef BIBTEXTITLE = "title={" TITLE "}";;
typedef TAGGEDTITLE = TITAG TITLE;;

typedef JOURNAL = NAME (WSP NAME)*;;
typedef BIBTEXJOURNAL = "journal={" JOURNAL "}";;
typedef TAGGEDJOURNAL = JOTAG JOURNAL;;

typedef FULLBIBTEX = "{" ((BIBTEXJOURNAL | BIBTEXAUTHORINFO | BIBTEXTITLE)",")* "}";;
typedef FULLTAGS = . | ((TAGGEDAUTHORDEFNS | TAGGEDTITLE | TAGGEDJOURNAL)
(("\n" (TAGGEDAUTHORDEFNS | TAGGEDTITLE | TAGGEDJOURNAL))*)) ;;

bibtex_to_readable_au = [BIBTEXAUTHORINFO <=> TAGGEDAUTHORDEFNS
{"author={Foster, Nathan and Pierce, Benjamin and Bohannon, Aaron}" <->
"au - Nathan Foster
 au - Benjamin Pierce
 au - Aaron Bohannon"}]

bibtext_to_readable_title = [BIBTEXTITLE <=> TAGGEDTITLE
{"title={Boomerang Resourceful Lenses For String Data}" <->
 "ti - Boomerang Resourceful Lenses For String Data"}]

journal_to_readable_journal = [BIBTEXJOURNAL <=> TAGGEDJOURNAL
{"journal={Principals Of Programming Languages}" <->
 "jo - Principals Of Programming Languages"}]

bibtext_to_tagged_tester= [FULLBIBTEX <=> FULLTAGS {
"{author={Foster, Nathan and Pierce, Benjamin and Bohannon, Aaron},title={Boomerang Resourceful Lenses For String Data},journal={Principals Of Programming Languages},}"
<->
"au - Nathan Foster
 au - Benjamin Pierce
 au - Aaron Bohannon
ti - Boomerang Resourceful Lenses For String Data
jo - Principals Of Programming Languages"
,
"{title={Boomerang Resourceful Lenses For String Data},}"
<->
"ti - Boomerang Resourceful Lenses For String Data"
}]

test bibtext_to_tagged_tester
{"{author={Foster, Nathan and Pierce, Benjamin and Bohannon, Aaron},}"
<->
"au - Nathan Foster
 au - Benjamin Pierce
 au - Aaron Bohannon",

"{title={Boomerang Resourceful Lenses For String Data},}"
<->
"ti - Boomerang Resourceful Lenses For String Data",

"{journal={Principals Of Programming Languages},}"
<->
"jo - Principals Of Programming Languages"
};;
