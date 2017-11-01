#use "base.decls"
#use "util.decls"

typedef USERNAME = (LOWERCASE | UPPERCASE | "_" | "." | "-" | ":" | "/" | "+" | DIGIT | "=" | "*")+;;

typedef NONEMPTY_USERNAMES = USERNAME ("," USERNAME)*;;

typedef CONF = (WORD NONEMPTY_SAMELINE_WSP WORD NONEMPTY_SAMELINE_WSP USERNAME ("" | (NONEMPTY_SAMELINE_WSP NONEMPTY_USERNAMES)) "\n")*;;
test CONF matches "host        dhcp    user      moreUsers
hostname1     0     user1     anotheruser,athirduser
hostname2     1     user2     stillanotheruser
";;

typedef HOST_DICT = "{\"host\"=\"" WORD "\"}";;
typedef DHCP_DICT = "{\"dhcp\"=\"" WORD "\"}";;
typedef USER_DICT = "{\"user\"=\"" USERNAME "\"}";;
typedef MORE_USERS_DICT = "{\"moreusers\"=\"" USERNAME "\"}";;

typedef CONF_DICT = ("{" HOST_DICT NONEMPTY_SAMELINE_WSP DHCP_DICT NONEMPTY_SAMELINE_WSP USER_DICT ("" | (NONEMPTY_SAMELINE_WSP MORE_USERS_DICT MORE_USERS_DICT*)) "}")*;;

backuppchosts_map = [CONF <=> CONF_DICT
{
"host        dhcp    user      moreUsers
hostname1     0     user1     anotheruser,athirduser
hostname2     1     user2     stillanotheruser
"
<->
"{{\"host\"=\"host\"}        {\"dhcp\"=\"dhcp\"}    {\"user\"=\"user\"}      {\"moreusers\"=\"moreUsers\"}}{{\"host\"=\"hostname1\"}     {\"dhcp\"=\"0\"}     {\"user\"=\"user1\"}     {\"moreusers\"=\"anotheruser\"}{\"moreusers\"=\"athirduser\"}}{{\"host\"=\"hostname2\"}     {\"dhcp\"=\"1\"}     {\"user\"=\"user2\"}     {\"moreusers\"=\"stillanotheruser\"}}"
}]