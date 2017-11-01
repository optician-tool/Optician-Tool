#use "base.decls"
#use "util.decls"

typedef LINKAGE = FOLDER " " WORD;;
typedef CELLALIASCONF = ((LINKAGE | COMMENT | .) "\n")*;;
typedef LINKAGEDICT = "{\"target\"=\""FOLDER"\"{\"linkname=\""WORD"\"}}";;
typedef CELLALIASDICT = (COMMENT_DICT|LINKAGEDICT|EMPTYDICT)*;;

afs_cellalias = [CELLALIASDICT <=> CELLALIASCONF {}]
