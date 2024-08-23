pragma Goals:printall.

require import AllCore.
require import Constants.
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

axiom q_eq_fieldq_p: Q = FieldQ.p.
axiom r_eq_fieldr_p: R = FieldR.p.    
lemma prime_q : prime Q by rewrite q_eq_fieldq_p; exact FieldQ.prime_p.
lemma prime_r : prime R by rewrite r_eq_fieldr_p; exact FieldR.prime_p.
  
op (^) (x : FieldR.F) (k : int) = FieldR.exp x k axiomatized by RexpE.

op OMEGAFr = FieldR.inF Constants.OMEGA axiomatized by omegaFrE.
op DOMAIN_SIZEFr = FieldR.inF DOMAIN_SIZE axiomatized by domain_sizeFrE.

lemma omega_eq_omegaFr : FieldR.asint OMEGAFr = OMEGA. 
proof.
  rewrite omegaFrE FieldR.inFK /OMEGA -r_eq_fieldr_p /Constants.R. progress. 
qed.

lemma domain_eq_domainFr : FieldR.asint DOMAIN_SIZEFr = DOMAIN_SIZE.
proof.
  rewrite domain_sizeFrE FieldR.inFK /DOMAIN_SIZE -r_eq_fieldr_p /Constants.R. progress.
qed.
