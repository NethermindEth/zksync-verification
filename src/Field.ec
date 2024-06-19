pragma Goals:printall.

require import Constants.
require export ZModP.

clone ZModField as Zr with 
  op p <- Constants.r 
  rename "zmod" as "Fr"
  rename "ZModp" as "Zr"
  proof prime_p by apply prime_r.

op (^) (x : Zr.Fr) (k : int) = Zr.exp x k axiomatized by expE.

(* op loge (x : group) : exp = inzmod (log x) *)
(* axiomatized by logE. *)
