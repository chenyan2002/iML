datatype 'a list = Nil | Cons of 'a * 'a list $C

fun map f l =
  case l of
    Nil => Nil
  | Cons (h,t) => Cons (f h, map f t)

val a:int $C = 1
val b:int $S = 2
(* val c = a + b *)

