pragma Goals:printall.

require import AllCore Int IntDiv ZModP.
require import Constants.

clone include ZModField  with 
  op p <- R 
  rename "zmod" as "Fr"
  rename "ZModp" as "Zr"
  proof prime_p by apply prime_r.
   
op (^) (x : Fr) (k : int) = exp x k axiomatized by expE.

op OMEGAFr = inFr OMEGA axiomatized by omegaFrE.
op DOMAIN_SIZEFr = inFr DOMAIN_SIZE axiomatized by domain_sizeFrE.

lemma omega_eq_omegaFr : asint OMEGAFr = OMEGA.
proof.
  rewrite omegaFrE /asint /inFr; have ->: OMEGA %% R = OMEGA by smt.
  rewrite Sub.insubdK //; smt.
qed.

lemma domain_eq_domainFr : asint DOMAIN_SIZEFr = DOMAIN_SIZE.
proof.
  rewrite domain_sizeFrE /asint /inFr; have ->: DOMAIN_SIZE %% R = DOMAIN_SIZE by smt.
  rewrite Sub.insubdK //; smt.
qed.
