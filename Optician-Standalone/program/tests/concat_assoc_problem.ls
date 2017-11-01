typedef A = "a";;
typedef B = "b";;
typedef C = "c";;

x = [A (B C) <=> (A B) C {}]

test x
{
"abc" <-> "abc"
};;