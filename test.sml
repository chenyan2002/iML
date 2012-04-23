datatype 'a list = Nil | Cons of 'a * 'a list $C
val tuple : int $C * int $S = (1,2)
and bar = {x=1,y=2}
and l = Cons(1, Cons (2, Cons (3, Nil)))

fun inc x = x+1 

fun map f l =
  case l of
    Nil => Nil
  | Cons (h,t) => Cons (f h, map f t)

val l:int $S list $C = map inc l

val a:int $S = 1
val b:int $C = 2
val c = Int.+(a,b)
val a = "3 + 4"
val c:string $S = a

