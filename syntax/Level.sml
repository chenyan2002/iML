structure Level :> LEVEL =
struct
   datatype t = Stable
              | Changeable
              | LVar of LvVar.LvVar
              | Unknown
end
