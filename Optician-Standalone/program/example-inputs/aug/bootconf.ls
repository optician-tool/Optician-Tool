#use "base.decls"
#use "util.decls"

typedef BOOT_COMMAND = "boot" NONEMPTY_SAMELINE_WSP WORD (NONEMPTY_SAMELINE_WSP WORD)*;;
test BOOT_COMMAND matches "boot /bsd -s";;

typedef BASIC_COMMAND = ("echo" | "ls") NONEMPTY_SAMELINE_WSP WORD;;
test BASIC_COMMAND matches "echo 42";;
test BASIC_COMMAND matches "ls /";;

typedef MACHINE_COMMAND = "machine" NONEMPTY_SAMELINE_WSP WORD ("" | (NONEMPTY_SAMELINE_WSP WORD));;
test MACHINE_COMMAND matches "machine diskinfo";;
test MACHINE_COMMAND matches "machine comaddr 0xdeadbeef";;

typedef SET_COMMAND = "set" NONEMPTY_SAMELINE_WSP WORD NONEMPTY_SAMELINE_WSP WORD;;
test SET_COMMAND matches "set tty com0";;

typedef SINGLE_COMMAND = WORD;;
test SINGLE_COMMAND matches "help";;

typedef SSTY_COMMAND = "ssty" NONEMPTY_SAMELINE_WSP WORD ("" | (NONEMPTY_SAMELINE_WSP NUMBER));;
test SSTY_COMMAND matches "ssty /dev/cuaU0 115200";;
test SSTY_COMMAND matches "ssty /dev/cuaU0";;

typedef COMMAND =
  (BOOT_COMMAND
    | BASIC_COMMAND
    | MACHINE_COMMAND
    | SET_COMMAND
    | SINGLE_COMMAND
    | SSTY_COMMAND)
  "\n";;

typedef BOOT_DICT = "{\"boot\"" NONEMPTY_SAMELINE_WSP
                      "{\"image\"=\"" WORD "\"}"
                      (NONEMPTY_SAMELINE_WSP "{\"arg\"=\"" WORD "\"}")*
                      "}";;
typedef ECHO_DICT = "{" NONEMPTY_SAMELINE_WSP "\"echo\"=\"" WORD "\"}";;
typedef LS_DICT = "{" NONEMPTY_SAMELINE_WSP "\"ls\"=\"" WORD "\"}";;
typedef MACHINE_DICT = "{" NONEMPTY_SAMELINE_WSP "\"machine\"{\"" WORD "\"}}"
                         | "{\"machine\"{" NONEMPTY_SAMELINE_WSP "\"" WORD "\"=" NONEMPTY_SAMELINE_WSP "\"" WORD "\"}}";;
typedef SET_DICT = "{\"set\"{" NONEMPTY_SAMELINE_WSP "\"" WORD "\"=" NONEMPTY_SAMELINE_WSP "\"" WORD "\"}}";;
typedef SINGLE_DICT = "{\"" WORD "\"}";;
typedef SSTY_DICT = "{\"ssty\"{" NONEMPTY_SAMELINE_WSP "\"device\"=\"" WORD "\"}"
                      ("" | "{" NONEMPTY_SAMELINE_WSP "\"speed\"=\"" NUMBER "\"}") "}";;

typedef DICT = BOOT_DICT | ECHO_DICT | LS_DICT | MACHINE_DICT | SET_DICT | SINGLE_DICT | SSTY_DICT;;

command_map = [COMMAND <=> DICT {}]