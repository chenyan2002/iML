datatype 'a list = Nil | Cons of 'a * 'a list $C
val tuple = (1,2,3)
and bar = {x=1,y=2}
and l = [1,2,3]

fun id x = x

fun map f l =
  case l of
    Nil => Nil
  | Cons (h,t) => Cons (f h, map f t)

val a:int $C = 1
val b:int $S = 2
val c = a + b 
(*val c = 1 + 2*)

