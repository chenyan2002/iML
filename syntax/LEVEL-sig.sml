signature LEVEL =
sig
   datatype t = Stable
              | Changeable
              | LVar of LvVar.LvVar
              | Unknown
end
