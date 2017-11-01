#use "base.decls"

typedef LOCALFOLDER = (LOWERCASE | UPPERCASE | "_" | "." | "-")+;;
test LOCALFOLDER matches "extract-filename.txt";;

typedef DIRECTORY = ("/" | .) (LOCALFOLDER "/")*;;
typedef GLOBALFOLDER = DIRECTORY LOCALFOLDER;;
typedef FOLDER = ( (LOCALFOLDER "/")* LOCALFOLDER (. | "/") );;
test DIRECTORY matches "Users/amiltner/lens/tests/flashfill/extract-filename.txt/";;

typedef FILEANDFOLDER = ("file: " LOCALFOLDER "\nfolder: " DIRECTORY) | "empty directory given" | "root directory given";;
test FILEANDFOLDER matches "file: extract-filename.txt\nfolder: Users/amiltner/lens/tests/flashfill/";;

extract_file = [DIRECTORY <=> FILEANDFOLDER
{ "Users/amiltner/lens/tests/flashfill/extract-filename.txt/" <-> "file: extract-filename.txt\nfolder: Users/amiltner/lens/tests/flashfill/",
"/" <-> "root directory given"
 }]
