#use "base.decls"
#use "util.decls"

typedef NO_PLUSSTAR_WORD = (LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | DIGIT | "," | "=" | "*")(LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | "+" | DIGIT | "," | "=" | "*")*;;

typedef NO_COLON_COMMA_SLASH_CHAR =
  LOWERCASE | UPPERCASE | DIGIT | "_" | "." | "+"
    | "=" | "&";;

typedef FILE = NO_COLON_COMMA_SLASH_CHAR+;;

typedef NO_COMMA_EQ_WORD =
  (LOWERCASE | UPPERCASE | "_" | "." | "-" | "/" | "+" | ":" | DIGIT)+;;

typedef OPTION = NO_COMMA_EQ_WORD ("" | ("=" NO_COMMA_EQ_WORD));;

typedef OPTIONS =
  "" | (NONEMPTY_SAMELINE_WSP "-" OPTION ("," OPTION)*);;
test OPTIONS matches "";;
test OPTIONS matches " -hi,hello=what,m";;

typedef PATH = "/" | ("/" FILE ("/" FILE)*);;
test PATH matches "/";;
test PATH matches "/usr/local/moxill";;

typedef AREA = "" | (NONEMPTY_SAMELINE_WSP PATH OPTIONS);;

typedef HOST = (NO_COLON_COMMA_SLASH_CHAR+) ("" | ("(" NUMBER ")"));;
typedef HOSTS = "" | (HOST ("," HOST)*);;
test HOSTS matches "host1,host2(5)";;
test HOSTS matches "";;
test HOSTS matches "host1(2)";;

typedef LOCATION = HOSTS ":" PATH;;

typedef AUTOMOUNTER_ENTRY =
  (NO_PLUSSTAR_WORD
    OPTIONS
    ((AREA
      NONEMPTY_SAMELINE_WSP LOCATION)+));;

typedef MAP_ENTRY = "+" STRING;;

typedef AUTOMOUNTER = (("" | COMMENT | AUTOMOUNTER_ENTRY | MAP_ENTRY) "\n")*;;
test AUTOMOUNTER matches
"# 
# This is an automounter map and it has the following format
# key [ -mount-options-separated-by-comma ] location
# Details may be found in the autofs(5) manpage

# indirect map
cd      -fstype=iso9660,ro,nosuid,nodev :/dev/cdrom
kernel    -ro,soft,intr       ftp.kernel.org:/pub/linux
*       -fstype=auto,loop,ro    :/srv/distros/isos/&.iso

# direct map
/nfs/apps/mozilla             bogus:/usr/local/moxill

# replicated server
path    host1,host2,hostn:/path/path
path    host1,host2:/blah host3(1):/some/other/path
path    host1(5),host2(6),host3(1):/path/path

# multi-mount map
server    -rw,hard,intr       / -ro myserver.me.org:/
server    -rw,hard,intr       / -ro myserver.me.org:/ /usr myserver.me.org:/usr
server    -rw,hard,intr       / -ro myserver.me.org:/ \
                              /usr myserver.me.org:/usr \
                              /home myserver.me.org:/home

server    -rw,hard,intr       / -ro mywithdashserver.me.org:/

# included maps
+auto_home
";;

typedef MAP_ENTRY_DICT = "{\"+\"{\"map\"=\"" DELIMITED_STRING "\"}}";;

typedef LOCATION_DICT =
  "{\"location\""
    ("{\"host\"=\"" HOST "\"}")*
    ("{\"path\"=\"" PATH "\"}");;

location_map = [LOCATION <=> LOCATION_DICT
{
"host1(5),host2(6),host3(1):/path/path"
<->
"{\"location\"{\"host\"=\"host1(5)\"}{\"host\"=\"host2(6)\"}{\"host\"=\"host3(1)\"}{\"path\"=\"/path/path\"}"
}]

typedef OPTIONS_DICT =
  "" |
  NONEMPTY_SAMELINE_WSP ("{\"opt\"=\""
    NO_COMMA_EQ_WORD
    "\""
    ("" | "{\"value\"=\"" NO_COMMA_EQ_WORD "\"}" )
    "}")+;;

options_map = [OPTIONS <=> OPTIONS_DICT {}]

typedef AUTOMOUNTER_ENTRY_DICT =
  "{\"" NO_PLUSSTAR_WORD "\""
    OPTIONS_DICT
    ("{"
      ("" | (NONEMPTY_SAMELINE_WSP "\"" PATH "\"" OPTIONS_DICT))
      NONEMPTY_SAMELINE_WSP LOCATION_DICT
      "}")+;;

typedef AUTOMOUNTER = (("" | COMMENT | AUTOMOUNTER_ENTRY | MAP_ENTRY) "\n")*;;
typedef AUTOMOUNTER_DICT =
  "{" ("{ }" | COMMENT_DICT | AUTOMOUNTER_ENTRY_DICT | MAP_ENTRY_DICT)* "}";;

automounter_map = [AUTOMOUNTER <=> AUTOMOUNTER_DICT
{
"# 
# This is an automounter map and it has the following format
# key [ -mount-options-separated-by-comma ] location
# Details may be found in the autofs(5) manpage

# indirect map
cd      -fstype=iso9660,ro,nosuid,nodev :/dev/cdrom
kernel    -ro,soft,intr       ftp.kernel.org:/pub/linux
*       -fstype=auto,loop,ro    :/srv/distros/isos/&.iso

# direct map
/nfs/apps/mozilla             bogus:/usr/local/moxill

# replicated server
path    host1,host2,hostn:/path/path
path    host1,host2:/blah host3(1):/some/other/path
path    host1(5),host2(6),host3(1):/path/path

# multi-mount map
server    -rw,hard,intr       / -ro myserver.me.org:/
server    -rw,hard,intr       / -ro myserver.me.org:/ /usr myserver.me.org:/usr
server    -rw,hard,intr       / -ro myserver.me.org:/ \\
                              /usr myserver.me.org:/usr \\
                              /home myserver.me.org:/home

server    -rw,hard,intr       / -ro mywithdashserver.me.org:/

# included maps
+auto_home
"<->
"{{\"#comment\"=\"\"}{\"#comment\"=\"This is an automounter map and it has the following format\"}{\"#comment\"=\"key [ -mount-options-separated-by-comma ] location\"}{\"#comment\"=\"Details may be found in the autofs(5) manpage\"}{ }{\"#comment\"=\"indirect map\"}{\"cd\"      {\"opt\"=\"fstype\"{\"value\"=\"iso9660\"}}{\"opt\"=\"ro\"}{\"opt\"=\"nosuid\"}{\"opt\"=\"nodev\"}{ {\"location\"{\"path\"=\"/dev/cdrom\"}}{\"kernel\"    {\"opt\"=\"ro\"}{\"opt\"=\"soft\"}{\"opt\"=\"intr\"}{       {\"location\"{\"host\"=\"ftp.kernel.org\"}{\"path\"=\"/pub/linux\"}}{\"*\"       {\"opt\"=\"fstype\"{\"value\"=\"auto\"}}{\"opt\"=\"loop\"}{\"opt\"=\"ro\"}{    {\"location\"{\"path\"=\"/srv/distros/isos/&.iso\"}}{ }{\"#comment\"=\"direct map\"}{\"/nfs/apps/mozilla\"{             {\"location\"{\"host\"=\"bogus\"}{\"path\"=\"/usr/local/moxill\"}}{ }{\"#comment\"=\"replicated server\"}{\"path\"{    {\"location\"{\"host\"=\"host1\"}{\"host\"=\"host2\"}{\"host\"=\"hostn\"}{\"path\"=\"/path/path\"}}{\"path\"{    {\"location\"{\"host\"=\"host1\"}{\"host\"=\"host2\"}{\"path\"=\"/blah\"}}{ {\"location\"{\"host\"=\"host3(1)\"}{\"path\"=\"/some/other/path\"}}{\"path\"{    {\"location\"{\"host\"=\"host1(5)\"}{\"host\"=\"host2(6)\"}{\"host\"=\"host3(1)\"}{\"path\"=\"/path/path\"}}{ }{\"#comment\"=\"multi-mount map\"}{\"server\"    {\"opt\"=\"rw\"}{\"opt\"=\"hard\"}{\"opt\"=\"intr\"}{       \"/\" {\"opt\"=\"ro\"} {\"location\"{\"host\"=\"myserver.me.org\"}{\"path\"=\"/\"}}{\"server\"    {\"opt\"=\"rw\"}{\"opt\"=\"hard\"}{\"opt\"=\"intr\"}{       \"/\" {\"opt\"=\"ro\"} {\"location\"{\"host\"=\"myserver.me.org\"}{\"path\"=\"/\"}}{ \"/usr\" {\"location\"{\"host\"=\"myserver.me.org\"}{\"path\"=\"/usr\"}}{\"server\"    {\"opt\"=\"rw\"}{\"opt\"=\"hard\"}{\"opt\"=\"intr\"}{       \"/\" {\"opt\"=\"ro\"} {\"location\"{\"host\"=\"myserver.me.org\"}{\"path\"=\"/\"}}{ \
                              \"/usr\" {\"location\"{\"host\"=\"myserver.me.org\"}{\"path\"=\"/usr\"}}{ \
                              \"/home\" {\"location\"{\"host\"=\"myserver.me.org\"}{\"path\"=\"/home\"}}{ }{\"server\"    {\"opt\"=\"rw\"}{\"opt\"=\"hard\"}{\"opt\"=\"intr\"}{       \"/\" {\"opt\"=\"ro\"} {\"location\"{\"host\"=\"mywithdashserver.me.org\"}{\"path\"=\"/\"}}{ }{\"#comment\"=\"included maps\"}{\"+\"{\"map\"=\"auto_home\"}}}"
}]