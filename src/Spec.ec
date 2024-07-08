pragma Goals:printall.

require import AllCore Int Constants Field.

import Zr.

theory Primops.
op reverted: bool.
end Primops.

(* Mid-level *)
op evalLagrange_Mspec_invalid (z : int) : bool = ((((z ^ domain_size) %% r) - 1) %% r = 0).

op evalLagrange_Mspec_valid (i z r : int) : bool =
  let zd   : int = (z ^ domain_size) %% r in
  let zd1  : int = (zd - 1) %% r in
  let oi   : int = (omega ^ i) %% r in
  let zoi  : int = (z - oi) %% r in
  let oizd : int = (oi * zd1) %% r in
  let dzoi : int = (domain_size * zoi) %% r in
  !((zd - 1) %% r = 0) /\ r = oizd %/ dzoi.

op evalLagrange_Mspec (i z r : int) : bool =
  (Primops.reverted = true => evalLagrange_Mspec_invalid z)
  /\
  (Primops.reverted = false => evalLagrange_Mspec_valid i z r).

(* High-level *)
op evalLagrange_Hspec_invalid (z : Fr) : bool = ((z ^ domain_size) - one = zero).

op evalLagrange_Hspec_valid (i : int) (z r : Fr) : bool =
  !((z ^ domain_size) - one = zero) /\
  r = ((inFr omega ^ i) * ((z ^ domain_size) - one)) / (inFr domain_size * (z - (inFr omega ^ i))).

op evalLagrange_Hspec (i : int) (z r: Fr) : bool =
  (Primops.reverted = true => evalLagrange_Hspec_invalid z)
  /\
  (Primops.reverted = false => evalLagrange_Hspec_valid i z r).
