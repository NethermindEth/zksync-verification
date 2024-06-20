pragma Goals:printall.

require import AllCore Int IntDiv Constants Field.

search exp.

theory Primops.
op reverted: bool.
end Primops.

(* Mid-level *)
op evalLagrange_Mspec_invalid (z : int) : bool = (z^domain_size - 1) %% r = 0.

op evalLagrange_Mspec_valid (i z r : int) : bool =
  let num  : int = (omega^i * (z^domain_size - 1)) %% r in
  let invd : int = (domain_size * (z - omega^i)^(r - 2)) %% r in
  !((z^domain_size - 1) %% r = 0) /\ r = (num * invd) %% r.

op evalLagrange_Mspec (i z r : int) : bool =
  (Primops.reverted = true => evalLagrange_Mspec_invalid z)
  /\
  (Primops.reverted = false => evalLagrange_Mspec_valid i z r).

(* High-level *)
op evalLagrange_Hspec_invalid (z : Fr) : bool = ((z ^ domain_size) - one = zero).

op evalLagrange_Hspec_valid (i : int) (z r : Fr) : bool =
  !(z^domain_size - one = zero) /\ r = (omegaFr^i * (z^domain_size - one)) / (domainFr * (z - omegaFr^i)).

op evalLagrange_Hspec (i : int) (z r: Fr) : bool =
  (Primops.reverted = true => evalLagrange_Hspec_invalid z)
  /\
  (Primops.reverted = false => evalLagrange_Hspec_valid i z r).
