#use "base.decls" 

typedef X = UPPERCASE;;

typedef DELIMITED_STRING = (UPPERCASE | LOWERCASE | DIGIT | "\\\"" | " ")*;;
typedef COMMENT_KVP = "\"#comment\" = \"" DELIMITED_STRING "\"";;
typedef TEXTCHAR = (UPPERCASE | LOWERCASE | " " | "\n" | DIGIT);;
typedef TEXT = TEXTCHAR*;;
typedef NONEMPTYTEXT = TEXTCHAR+;;

typedef NAME = (UPPERCASE | LOWERCASE | DIGIT)+;;

typedef XML_ATTRIBUTE_KVP = NAME"=\""TEXT"\"";;
test XML_ATTRIBUTE_KVP matches "attribute=\"myattribute\"";;

typedef XML_ATTRIBUTE_LIST = (" " XML_ATTRIBUTE_KVP)*;;

typedef XML_ELEMENT = "<" NAME XML_ATTRIBUTE_LIST ">";;
test XML_ELEMENT matches "<hello attribute=\"myattribute\">";;

typedef XML_END_ELEMENT = "</" NAME ">";;
test XML_END_ELEMENT matches "</hello>";;

typedef XML_CONTENTLESS_ELEMENT = "<" NAME XML_ATTRIBUTE_LIST "/>";;
test XML_CONTENTLESS_ELEMENT matches "<hello attribute=\"myattribute\"/>";;

typedef XML_INNER_ELEMENT = (XML_ELEMENT TEXT XML_END_ELEMENT) | XML_CONTENTLESS_ELEMENT;;
test XML_INNER_ELEMENT matches "<hello></hello>";;
test XML_INNER_ELEMENT matches "<hello/>";;

typedef SINGLE_ATTRIBUTE_DICT = "{\""NAME"\"=\"" TEXT "\"}";;
test SINGLE_ATTRIBUTE_DICT matches "{\"attribute\"=\"value\"}";;

typedef FULL_ATTRIBUTE_DICT = "{\"#attribute\"" SINGLE_ATTRIBUTE_DICT+ "}";;
test FULL_ATTRIBUTE_DICT matches "{\"#attribute\"{\"attribute\"=\"value\"}}";;

typedef ENDBRACE_DICT = "{\"endbrace\"=\"" NAME "\"}";;
test ENDBRACE_DICT matches "{\"endbrace\"=\"test\"}";;

typedef NONEMPTY_TEXT_DICT = "{\"#text\"=\""NONEMPTYTEXT"\"}";;
test NONEMPTY_TEXT_DICT matches "{\"#text\"=\"text\"}";;

typedef INNER_XML_DICT = "{" "\""NAME"\"" (FULL_ATTRIBUTE_DICT|.) (((NONEMPTY_TEXT_DICT|.)ENDBRACE_DICT)|.) "}";;
test INNER_XML_DICT matches "{\"element\"}";;

typedef SECONDLEVEL_XML_DICT =
"{" "\""NAME"\"" (FULL_ATTRIBUTE_DICT|.) (((NONEMPTY_TEXT_DICT|.|(INNER_XML_DICT+))ENDBRACE_DICT)|.) "}";;
test SECONDLEVEL_XML_DICT matches "{\"element\"}";;
test SECONDLEVEL_XML_DICT matches "{\"element\"{\"#attribute\"{\"attribute\"=\"value\"}}}";;
test SECONDLEVEL_XML_DICT matches "{\"element\"{\"#attribute\"{\"attribute\"=\"value\"}}{\"endbrace\"=\"test\"}}";;
test SECONDLEVEL_XML_DICT matches "{\"element\"{\"#attribute\"{\"attribute\"=\"value\"}}{\"element\"}{\"endbrace\"=\"test\"}}";;

typedef THIRDLEVEL_XML_DICT =
"{" "\""NAME"\"" (FULL_ATTRIBUTE_DICT|.) (((NONEMPTY_TEXT_DICT|.|(SECONDLEVEL_XML_DICT+))ENDBRACE_DICT)|.) "}";;

typedef XML_SECONDLEVEL_ELEMENT = (XML_ELEMENT
				  (TEXT | (XML_INNER_ELEMENT+))
			          XML_END_ELEMENT) | XML_CONTENTLESS_ELEMENT;;

typedef XML_THIRDLEVEL_ELEMENT = (XML_ELEMENT
				  (TEXT | (XML_SECONDLEVEL_ELEMENT+))
			          XML_END_ELEMENT) | XML_CONTENTLESS_ELEMENT;;


map_inner = [XML_INNER_ELEMENT <=> INNER_XML_DICT {}]
map_outer = [XML_SECONDLEVEL_ELEMENT <=> SECONDLEVEL_XML_DICT {}]
map_third = [XML_THIRDLEVEL_ELEMENT <=> THIRDLEVEL_XML_DICT {}]
