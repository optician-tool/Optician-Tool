#use "base.decls"
#use "util.decls"

typedef THINGANDAMOUNT = TEXT DIGIT NUMERICTEXT;;
typedef AMOUNT_EXTRACTED = "amount: "DIGIT NUMERICTEXT "\nworthless text: " TEXT;;

extract_amount = [THINGANDAMOUNT <=> AMOUNT_EXTRACTED
{
"hey look we sure have a lot of corn we have 35 OZ"
<->
"amount: 35 OZ\nworthless text: hey look we sure have a lot of corn we have "
}]
