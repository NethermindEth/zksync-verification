pragma Goals:printall.

require import AllCore Int IntDiv Constants Field.

op lagrangeM (i z : int) : int =
  let omi  = (OMEGA^i) %% R in
  let zd1  = (z^DOMAIN_SIZE - 1) %% R in
  let num  = (omi * zd1) %% R in
  let invd = ((DOMAIN_SIZE * (z - omi)) %% R)^(R - 2) %% R in
  (num * invd) %% R.

op lagrangeH (i : int) (z : Fr) : Fr =
  (OMEGAFr^i * (z^DOMAIN_SIZE - one)) / (DOMAIN_SIZEFr * (z - OMEGAFr^i)).

module EvaluateLagrangePolyOutOfDomain = {
  proc mid(i: int, z: int) : int option = {
    var r;
    
    if((z^DOMAIN_SIZE - 1)%%R = 0) {
      r <- None;
    } else {
      r <- Some (lagrangeM i z);
    }  
    return r;
  }

  proc high(i: int, z: Fr) : Fr option = {
    var r;
    
    if((z^DOMAIN_SIZE - one) = zero) {
      r <- None;
    } else {
      r <- Some (lagrangeH i z);
    }  
    return r;
  }
}.

(* Mid-level *)
(* op evalLagrange_Mspec_res (i z rs : int) : bool = *)
(*   let omi  = (omega^i) %% r in *)
(*   let zd1  = (z^domain_size - 1) %% r in *)
(*   let num  = (omi * zd1) %% r in *)
(*   let invd = ((domain_size * (z - omi)) %% r)^(r - 2) %% r in *)
(*   rs = (num * invd) %% r. *)

(* op evalLagrange_Mspec (i z rs : int) : bool = *)
(*   (!((z^domain_size - 1) %% r = 0) => !Primops.reverted /\ evalLagrange_Mspec_res i z rs) *)
(*   /\ *)
(*   ((z^domain_size - 1) %% r = 0 => Primops.reverted). *)

(* (* High-level *) *)
(* op evalLagrange_Hspec (i : int) (z rs : Fr) : bool = *)
(*   !(z^domain_size - one = zero) => *)
(*   rs = (omegaFr^i * (z^domain_size - one)) / (domain_sizeFr * (z - omegaFr^i)). *)
