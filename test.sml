datatype 'a list = Nil | Cons of 'a * 'a list $C
val tuple = (1,2,3)
and bar = {x=1,y=2}
and l = Cons(1, Cons (2, Cons (3, Nil)))

fun inc x = x+1

fun map f l =
  case l of
    Nil => Nil
  | Cons (h,t) => Cons (f h, map f t)

val _ = map inc l

val a:int $C = 1
val b:int $S = 2
val c = a+b
val a = "3 + 4"
val c = a^"test"
