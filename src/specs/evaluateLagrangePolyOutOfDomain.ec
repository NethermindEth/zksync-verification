pragma Goals:printall.

require import AllCore Int IntDiv Wheels Constants Field.

(* Mid-level *)
op evalLagrange_Mspec_res (i z rs : int) : bool =
  let omi  = (omega^i) %% r in
  let zd1  = (z^domain_size - 1) %% r in
  let num  = (omi * zd1) %% r in
  let invd = ((domain_size * (z - omi)) %% r)^(r - 2) %% r in
  rs = (num * invd) %% r.

op evalLagrange_Mspec (i z rs : int) : bool =
  (!((z^domain_size - 1) %% r = 0) => !Primops.reverted /\ evalLagrange_Mspec_res i z rs)
  /\
  ((z^domain_size - 1) %% r = 0 => Primops.reverted).

(* High-level *)
op evalLagrange_Hspec (i : int) (z rs : Fr) : bool =
  !(z^domain_size - one = zero) =>
  rs = (omegaFr^i * (z^domain_size - one)) / (domain_sizeFr * (z - omegaFr^i)).
