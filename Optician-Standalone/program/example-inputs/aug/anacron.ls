#use "base.decls"
#use "util.decls"

typedef ENV_VAR_CONF = ENV_VAR"="STRING;;
test ENV_VAR_CONF matches "PATH=/path to/fOlder";;
typedef TIMEFRAME = NUMBER | ("@"WORD);;
typedef CRON_ENTRY = TIMEFRAME "	" TIMEFRAME "	" WORD "	" STRING;;
test CRON_ENTRY matches "@monthly	15	cron.monthly	nice run-parts --report /etc/cron.monthly";;
typedef ANACRON_CONF = ((COMMENT | . | CRON_ENTRY | ENV_VAR_CONF) "\n")*;;

typedef ENV_VAR_DICT = "{\"" ENV_VAR "\"=\"" STRING "\"}";;
test ENV_VAR_DICT matches "{\"PATH\"=\"/path to/fOlder\"}";;
typedef PERIOD_DICT = "{\"" (("period\"=\"" NUMBER)|("period_name\"=\"" WORD)) "\"}";;
test PERIOD_DICT matches "{\"period_name\"=\"monthly\"}";;
typedef DELAY_DICT = "{\"delay\"=\"" TIMEFRAME "\"}";;
test DELAY_DICT matches "{\"delay\"=\"15\"}";;
typedef JOB_ID_DICT = "{\"job-identifier\"=\"" WORD "\"}";;
test JOB_ID_DICT matches "{\"job-identifier\"=\"cron.monthly\"}";;
typedef CRON_ENTRY_DICT = "{\"entry\"=\""STRING"\""PERIOD_DICT DELAY_DICT JOB_ID_DICT "}";;
test CRON_ENTRY_DICT matches "{\"entry\"=\"nice run-parts --report /etc/cron.monthly\"{\"period_name\"=\"monthly\"}{\"delay\"=\"15\"}{\"job-identifier\"=\"cron.monthly\"}}";;
typedef ANACRON_DICT = (COMMENT_DICT | CRON_ENTRY_DICT | EMPTYDICT | ENV_VAR_DICT)*;;

afs_cellalias = [ANACRON_CONF <=> ANACRON_DICT {
"# comment
PATH=/path to/fOlder

@monthly	15	cron.monthly	nice run-parts --report /etc/cron.monthly
" <->
"{\"#comment\"=\"comment\"}{\"PATH\"=\"/path to/fOlder\"}{}{\"entry\"=\"nice run-parts --report /etc/cron.monthly\"{\"period_name\"=\"monthly\"}{\"delay\"=\"15\"}{\"job-identifier\"=\"cron.monthly\"}}"}]
