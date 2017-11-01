#use "base.decls"

typedef YEAR = DIGIT DIGIT DIGIT DIGIT;;
typedef MONTH = DIGIT + "11" + "12";;
typedef DAY = (("1" + "2" + "3") DIGIT) + "31";;
typedef WEEKDAYS = "sunday" + "monday" + "tuesday" + "wednesday" + "thursday" + "friday" + "saturday";;

english_to_british = [MONTH "/" DAY "/" YEAR <=> DAY "/" MONTH "/" YEAR {}]
