pragma Goals:printall.

require import AllCore Int IntDiv ZModP.
require import Constants.

print r.

clone include ZModField  with 
  op p <- r 
  rename "zmod" as "Fr"
  rename "ZModp" as "Zr"
  proof prime_p by apply prime_r.
   
op (^) (x : Fr) (k : int) = exp x k axiomatized by expE.

op omegaFr = inFr omega axiomatized by omegaFrE.
op domain_sizeFr = inFr domain_size axiomatized by domain_sizeFrE.

lemma omega_eq_omegaFr : asint omegaFr = omega.
proof.
  rewrite omegaFrE /asint /inFr; have ->: omega %% r = omega by smt.
  rewrite Sub.insubdK //; smt.
qed.

lemma domain_eq_domainFr : asint domain_sizeFr = domain_size.
proof.
  rewrite domain_sizeFrE /asint /inFr; have ->: domain_size %% r = domain_size by smt.
  rewrite Sub.insubdK //; smt.
qed.
