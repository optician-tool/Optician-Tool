#use "base.decls"
#use "util.decls"

typedef KVP_ELEMENT = (" " WORD " = " WORD ";");;

typedef KVP_LIST_CONF =
  "{" (KVP_ELEMENT | (COMMENT "\n") | "\n")* "}";;

typedef KVP_ELEMENT_DICT = "{\"" WORD "\"=\"" WORD "\"}";;

typedef KVP_LIST_DICT =
  "{" (KVP_ELEMENT_DICT | COMMENT_DICT | "{}")* "}";;

typedef MOUNT_CONF =
  "mount" KVP_LIST_CONF;;

typedef MOUNT_DICT =
  "{\"mount\"" KVP_LIST_DICT "}";;

typedef CONTROLLER_NAME =
  ("cpuacct" | "cpu" | "devices" | "ns" | "cpuset" | "memory" | "freezer"
    | "net_cls" | "blkio" | "hugetlb" | "perf_event");;

typedef CONTROLLER_CONF =
  CONTROLLER_NAME KVP_LIST_CONF;;

typedef CONTROLLER_DICT =
  "{\"controller\"=\"" CONTROLLER_NAME "\"" KVP_LIST_DICT "}";;

typedef TASK_CONF = "task" KVP_LIST_CONF;;
typedef TASK_DICT = "{\"task\"" KVP_LIST_DICT "}";;

task_map = [TASK_CONF <=> TASK_DICT {}]

typedef ADMIN_CONF = "admin" KVP_LIST_CONF;;
typedef ADMIN_DICT = "{\"admin\"" KVP_LIST_DICT "}";;

typedef PERM_CONF =
  "perm{"
    ((COMMENT | "") "\n")*
    TASK_CONF
    ((COMMENT | "") "\n")*
    ADMIN_CONF
    ((COMMENT | "") "\n")*
  "}";;

typedef PERM_DICT =
  "{\"perm\""
    (COMMENT_DICT | "{}")*
    TASK_DICT
    (COMMENT_DICT | "{}")*
    ADMIN_DICT
    (COMMENT_DICT | "{}")*
  "}";;

typedef GROUP_CONF =
  "group " WORD " {"
  ("\n" | (COMMENT "\n") | PERM_CONF | ADMIN_CONF)*
  "}";;

typedef GROUP_DICT =
  "{\"group\"=\"" WORD "\""
    ("{}" | COMMENT_DICT | PERM_DICT | ADMIN_DICT)*
  "}";;

typedef CGCONFIG_CONF = (("" | COMMENT | GROUP_CONF | MOUNT_CONF) "\n")*;;
typedef CGCONFIG_DICT = "{" ("{}" | COMMENT_DICT | GROUP_DICT | MOUNT_DICT)* "}";;

cgconfig_map = [CGCONFIG_CONF <=> CGCONFIG_DICT {}]