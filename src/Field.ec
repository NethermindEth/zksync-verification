pragma Goals:printall.

<<<<<<< HEAD
require import AllCore Int IntDiv ZModP StdOrder.
require import Constants.

theory FieldR.
clone include ZModField with 
  op p <- R 
  rename "zmod" as "F"
  rename "ZModp" as "Zr"
  proof prime_p by apply prime_r.
end FieldR.

theory FieldQ.
clone include ZModField with 
  op p <- Q 
  rename "zmod" as "F"
  rename "ZModp" as "Zq"
  proof prime_p by apply prime_q.
end FieldQ.
  
op (^) (x : FieldR.F) (k : int) = FieldR.exp x k axiomatized by RexpE.

(* op OMEGAFr = inFr OMEGA axiomatized by omegaFrE. *)
(* op DOMAIN_SIZEFr = inFr DOMAIN_SIZE axiomatized by domain_sizeFrE. *)

(* lemma omega_eq_omegaFr : asint OMEGAFr = OMEGA. *)
(* proof. *)
(*   rewrite omegaFrE /asint /inFr; have ->: OMEGA %% R = OMEGA by smt. *)
(*   rewrite Sub.insubdK //; smt. *)
(* qed. *)

(* lemma domain_eq_domainFr : asint DOMAIN_SIZEFr = DOMAIN_SIZE. *)
(* proof. *)
(*   rewrite domain_sizeFrE /asint /inFr; have ->: DOMAIN_SIZE %% R = DOMAIN_SIZE by smt. *)
(*   rewrite Sub.insubdK //; smt. *)
(* qed. *)
=======
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
>>>>>>> 207ac17 (refined specs.)
