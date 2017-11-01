#use "base.decls"

typedef TEXT_FIELD_CHAR = (UPPERCASE | LOWERCASE | DIGIT | " " | "\n" | "\t");;
typedef TEXT_FIELD = TEXT_FIELD_CHAR*;;
typedef NONEMPTY_TEXT_FIELD = TEXT_FIELD_CHAR+;;

typedef NUMERIC_FIELD = NUMBER;;

typedef TITLE_LEGACY = "<Field Id=1>" TEXT_FIELD "</Field>";;
typedef TITLE_MODERN = "\"title\"=\"" NONEMPTY_TEXT_FIELD "\"";;
test TITLE_MODERN matches "\"title\"=\"title\"";;

typedef TYPE_LEGACY = "<Field Id=2>" TEXT_FIELD "</Field>";;
typedef TYPE_MODERN = "\"type\"=\"" NONEMPTY_TEXT_FIELD "\"";;

typedef ID_LEGACY = "<Field Id=3>" NUMERIC_FIELD "</Field>";;
typedef ID_MODERN = "\"id\"=\"" NUMERIC_FIELD "\"";;

typedef DESCRIPTION_LEGACY = "<Field Id=4>" TEXT_FIELD "</Field>";;
typedef DESCRIPTION_MODERN = "\"description\"=\"" NONEMPTY_TEXT_FIELD "\"";;

typedef WORKITEM_LEGACY =
"<WorkItem>"
  TITLE_LEGACY TYPE_LEGACY ID_LEGACY DESCRIPTION_LEGACY
"</WorkItem>";;
test WORKITEM_LEGACY matches "<WorkItem><Field Id=1></Field><Field Id=2></Field><Field Id=3>1</Field><Field Id=4></Field></WorkItem>";;

typedef WORKITEM_MODERN =
  "{"
    ("" | (DESCRIPTION_MODERN ","))
    (ID_MODERN ",")
    ("" | (TITLE_MODERN ","))
    ("" | (TYPE_MODERN ","))
  "}";;

legacy_converter = [WORKITEM_LEGACY <=> WORKITEM_MODERN
{
"<WorkItem><Field Id=1></Field><Field Id=2></Field><Field Id=3>1</Field><Field Id=4></Field></WorkItem>"
<->
"{\"id\"=\"1\",}",
"<WorkItem><Field Id=1>title</Field><Field Id=2></Field><Field Id=3>1</Field><Field Id=4></Field></WorkItem>"
<->
"{\"id\"=\"1\",\"title\"=\"title\",}",
"<WorkItem><Field Id=1>title</Field><Field Id=2>bug</Field><Field Id=3>1</Field><Field Id=4></Field></WorkItem>"
<->
"{\"id\"=\"1\",\"title\"=\"title\",\"type\"=\"bug\",}",
"<WorkItem><Field Id=1>title</Field><Field Id=2>bug</Field><Field Id=3>1</Field><Field Id=4>this is a bad bug</Field></WorkItem>"
<->
"{\"description\"=\"this is a bad bug\",\"id\"=\"1\",\"title\"=\"title\",\"type\"=\"bug\",}",
"<WorkItem><Field Id=1></Field><Field Id=2>bug</Field><Field Id=3>1</Field><Field Id=4>this is a bad bug</Field></WorkItem>"
<->
"{\"description\"=\"this is a bad bug\",\"id\"=\"1\",\"type\"=\"bug\",}",
"<WorkItem><Field Id=1>title</Field><Field Id=2></Field><Field Id=3>1</Field><Field Id=4>this is a bad bug</Field></WorkItem>"
<->
"{\"description\"=\"this is a bad bug\",\"id\"=\"1\",\"title\"=\"title\",}",
"<WorkItem><Field Id=1></Field><Field Id=2></Field><Field Id=3>1</Field><Field Id=4>this is a bad bug</Field></WorkItem>"
<->
"{\"description\"=\"this is a bad bug\",\"id\"=\"1\",}",
"<WorkItem><Field Id=1></Field><Field Id=2>bug</Field><Field Id=3>1</Field><Field Id=4></Field></WorkItem>"
<->
"{\"id\"=\"1\",\"type\"=\"bug\",}"
}]

