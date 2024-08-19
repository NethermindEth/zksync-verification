pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
require import StdOrder.
require import ZModP.

theory FieldR.
clone include ZModField
  rename "zmod" as "F"
  rename "ZModp" as "Zr".
end FieldR.

theory FieldQ.
clone include ZModField
  rename "zmod" as "F"
  rename "ZModp" as "Zq".
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
