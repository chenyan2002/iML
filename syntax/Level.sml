structure Level :> LEVEL =
struct
   datatype t = Stable
              | Changeable
              | LVar of LvVar.LvVar
              | Unknown

   fun toString lv = 
     case lv of
       Stable => "$S"
     | Changeable => "$C"
     | LVar v => LvVar.toString v
     | Unknown => "$?" 

end
