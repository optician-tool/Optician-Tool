#use "base.decls"
#use "util.decls"

typedef SIMPLE_KEY =
  "acquisitionport" | "bindacqaddress"
    | "bindaddress" | "bindcmdaddress" | "clientloglimit"
    | "combinelimit" | "commandkey"
    | "cmdport" | "corrtimeratio" | "driftfile"
    | "dumpdir" | "hwclockfile" | "include" | "keyfile"
    | "leapsecmode" | "leapsectz" | "linux_freq_scale"
    | "linux_hz" | "logbanner" | "logchange" | "logdir"
    | "maxclockerror" | "maxdistance" | "maxdrift"
    | "maxjitter" | "maxsamples" | "maxslewrate"
    | "maxupdateskew" | "minsamples" | "minsources"
    | "ntpsigndsocket" | "pidfile"
    | "port" | "reselectdist" | "rtcautotrim" | "rtcdevice"
    | "rtcfile" | "sched_priority" | "stratumweight" | "user"
    | "maxdelay" | "maxpoll" | "minpoll" | "maxsamples" | "minsamples"
    | "maxsources" | "offset" | "polltarget" | "port" | "presend"
    | "version";;

typedef CMD_FLAG =
  "auto_offline" | "iburst" | "noselect" | "offline" | "prefer"
    | "require" | "trust" | "xleave";;

typedef CMD_ARG =
  (SIMPLE_KEY (" " WORD)) | CMD_FLAG;;

typedef CMD_ARG_DICT =
  ("{\"" SIMPLE_KEY "\"=\"" WORD "\"}")
    | ("{\"" CMD_FLAG "\"}");;

typedef SERVER_CONF = "server " WORD (" " CMD_ARG)*;;
test SERVER_CONF matches "server ntp1.example.com";;
test SERVER_CONF matches "server ntp1.example.com iburst presend 2";;

typedef SERVER_DICT = "{\"server\"=\"" WORD "\"" (CMD_ARG_DICT)* "}";;

server_map = [SERVER_CONF <=> SERVER_DICT {}]

typedef PEER_CONF = "peer " WORD (" " CMD_ARG)*;;
typedef POOL_CONF = "pool " WORD (" " CMD_ARG)*;;