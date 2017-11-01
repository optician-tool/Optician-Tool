#use "base.decls"
#use "util.decls"

typedef CACHE_ENTRY = WORD ("" | NONEMPTY_SAMELINE_WSP WORD);;
test CACHE_ENTRY matches "dir /var/cache/fscache";;
test CACHE_ENTRY matches "brun 10%";;
test CACHE_ENTRY matches "secctx system_u:system_r:cachefiles_kernel_t:s0";;
typedef CACHE_FILES = ((COMMENT | CACHE_ENTRY | "") "\n")*;;
test CACHE_FILES matches "
# I am a comment
dir /var/cache/fscache
tAg mycache
brun 10%
bcull 7%
bstop 3%
frun 10%
fcull 7%
fstop 3%
nocull

secctx system_u:system_r:cachefiles_kernel_t:s0
";;

typedef CACHE_ENTRY_DICT = "{\"" WORD "\"}"
                         | "{" NONEMPTY_SAMELINE_WSP "\"" WORD "\"=\"" WORD "\"}";;

typedef CACHE_DICT = (CACHE_ENTRY_DICT | "{ }" | COMMENT_DICT)*;;

cache_map = [CACHE_FILES <=> CACHE_DICT {}]