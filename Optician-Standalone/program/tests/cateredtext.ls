typedef A = "x" | "y";;
typedef B = "z" | "w";;
typedef C = "m" | "n";;
typedef D = "t" | "w";;

x = [A | B <=> C | D {}]

test x
{
"x" <-> "m",
"z" <-> "t"
};;