#use "base.decls"

typedef LOCALFOLDER = (LOWERCASE | UPPERCASE | "_" | "." | "-")+;;
test LOCALFOLDER matches "extract-filename.txt";;

typedef DIRECTORY = ("/" | .) (LOCALFOLDER "/")*;;
typedef NONEMPTYDIRECTORY = ("/" | .) (LOCALFOLDER) ("/" LOCALFOLDER)*;;
typedef GLOBALFOLDER = DIRECTORY LOCALFOLDER;;
typedef FOLDER = ( (LOCALFOLDER "/")* LOCALFOLDER (. | "/") );;
test DIRECTORY matches "Users/amiltner/lens/tests/flashfill/extract-filename.txt/";;

typedef FILEANDFOLDER = ("file: " LOCALFOLDER "\nfolder: " DIRECTORY);;
test FILEANDFOLDER matches "file: extract-filename.txt\nfolder: Users/amiltner/lens/tests/flashfill/";;

extract_file = [NONEMPTYDIRECTORY <=> FILEANDFOLDER
{ "/Users/amiltner/lens/tests/flashfill/extract-filename.txt" <-> "file: extract-filename.txt\nfolder: /Users/amiltner/lens/tests/flashfill/",
  "tests/flashfill/extract-filename.txt" <-> "file: extract-filename.txt\nfolder: tests/flashfill/"
 }]
