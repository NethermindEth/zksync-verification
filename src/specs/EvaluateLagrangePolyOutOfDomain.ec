pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
require import Constants.
require import Utils.
require import Modexp.
require import PurePrimops.
require import RevertWithMessage.
require import UInt256.
require import Verifier.
require import YulPrimops.

import MemoryMap.

module EvaluateLagrangePolyOutOfDomain = {
  proc low(polyNum: uint256, at: uint256): uint256 = {
  var ret, omegaPower, tmp267, _10, denominator;
    omegaPower <- (W256.of_int 1);
    if ((bool_of_uint256 polyNum))
    {
      omegaPower <@ Modexp.low((W256.of_int Constants.OMEGA), polyNum);
    }
    
    tmp267 <@ Modexp.low(at, (W256.of_int Constants.DOMAIN_SIZE));
    ret <- (PurePrimops.addmod tmp267 ((W256.of_int Constants.R) - W256.one) (W256.of_int Constants.R));
    if ((bool_of_uint256 (PurePrimops.iszero ret)))
    {
      RevertWithMessage.low(W256.of_int 28, W256.of_int STRING);
    }
    
    ret <- (PurePrimops.mulmod ret omegaPower (W256.of_int Constants.R));
    _10 <- ((W256.of_int Constants.R) - omegaPower);
    denominator <- (PurePrimops.addmod at _10 (W256.of_int Constants.R));
    denominator <- (PurePrimops.mulmod denominator (W256.of_int Constants.DOMAIN_SIZE) (W256.of_int Constants.R));
    denominator <@ Modexp.low(denominator, ((W256.of_int Constants.R) - (W256.of_int 2)));
    ret <- (PurePrimops.mulmod ret denominator (W256.of_int Constants.R));
    return ret;
  }

  (* proc low'(polyNum: uint256, at: uint256): uint256 = { *)
  (* var ret, omegaPower, tmp267, _10, denominator; *)
  (*   tmp267 <@ Modexp.low(at, (W256.of_int Constants.DOMAIN_SIZE)); *)

  (*   omegaPower <- (W256.of_int 1); *)
  (*   if ((bool_of_uint256 polyNum)) *)
  (*   { *)
  (*     omegaPower <@ Modexp.low((W256.of_int Constants.OMEGA), polyNum); *)
  (*   } *)
    
  (*   ret <- (PurePrimops.addmod tmp267 ((W256.of_int Constants.R) - W256.one) (W256.of_int Constants.R)); *)
  (*   if ((bool_of_uint256 (PurePrimops.iszero ret))) *)
  (*   { *)
  (*     RevertWithMessage.low(W256.of_int 28, W256.of_int STRING); *)
  (*   } *)
    
  (*   ret <- (PurePrimops.mulmod ret omegaPower (W256.of_int Constants.R)); *)
  (*   _10 <- ((W256.of_int Constants.R) - omegaPower); *)
  (*   denominator <- (PurePrimops.addmod at _10 (W256.of_int Constants.R)); *)
  (*   denominator <- (PurePrimops.mulmod denominator (W256.of_int Constants.DOMAIN_SIZE) (W256.of_int Constants.R)); *)
  (*   denominator <@ Modexp.low(denominator, ((W256.of_int Constants.R) - (W256.of_int 2))); *)
  (*   ret <- (PurePrimops.mulmod ret denominator (W256.of_int Constants.R)); *)
  (*   return ret; *)
  (* } *)
  
  proc mid(polyNum: int, at: int): int option = {
    var r, omegaPolyNum, atDomainSize, zd1, num, den, inv;

    omegaPolyNum <- (OMEGA ^ polyNum) %% R; 
    atDomainSize <- (at ^ DOMAIN_SIZE) %% R; 
    
    zd1 <- (atDomainSize - 1) %% R;
    
    if(zd1 = 0) {
      r <- None;
    } else {
      num <- (omegaPolyNum * zd1) %% R;
      den <- (DOMAIN_SIZE * (at - omegaPolyNum)) %% R;
      inv <- den^(R - 2) %% R;
      r <- Some ((num * inv) %% R);
    }  
    return r;
  }
}.
    
lemma evaluateLagrangePolyOutOfDomain_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_evaluateLagrangePolyOutOfDomain ~ EvaluateLagrangePolyOutOfDomain.low :
      ={arg, glob EvaluateLagrangePolyOutOfDomain} ==>
      ={res, glob EvaluateLagrangePolyOutOfDomain}
    ].
        proc.
        seq 2 2: (#pre /\ usr_omegaPower{1} = omegaPower{2}).
        sp.
      case (bool_of_uint256 polyNum{2}).
        rcondt{1} 1. by progress.
        rcondt{2} 1. by progress.
        sp. wp.
        call modexp_extracted_equiv_low. skip. progress. rewrite /Constants.OMEGA. reflexivity.
      (* case !bool_of_uint256 polyNum{2}). *)
        rcondf{1} 1. by progress.
        rcondf{2} 1. by progress.
        skip. by progress.
      (* finished seq 2 2 *)
        wp.
        call modexp_extracted_equiv_low.
        seq 8 2: (#pre /\ ={tmp267} /\ usr_res{1} = ret{2} /\ _7{1} = PurePrimops.iszero (usr_res{1}) /\ _2{1} = W256.of_int Constants.R /\ _5{1} = W256.of_int Constants.DOMAIN_SIZE ).
        wp. sp.
        call modexp_extracted_equiv_low. skip. progress.
        rewrite /Constants.DOMAIN_SIZE. by reflexivity.
        congr. rewrite /Constants.R. by smt (@W256).
        rewrite /Constants.R. by reflexivity.
        rewrite /Constants.R. by reflexivity.
      (* finished seq 8 2 *)
        if. by progress.
        sp.
        wp.
        call revertWithMessage_extracted_equiv_low. skip. by progress.
        sp. skip. by progress.
    qed.

lemma modexp_same (m: mem) (v1 v2 p1 p2 r1 r2 : uint256) : 
    modexp_memory_footprint (modexp_memory_footprint m v1 p1 r1) v2 p2 r2 =
    modexp_memory_footprint m v2 p2 r2.
proof. admit. qed.

lemma modexp_pspec (m : mem) (base power : uint256) :
    phoare [ Modexp.low :
      arg = (base, power) /\
      Primops.memory = m /\
      !Primops.reverted
      ==>
      !Primops.reverted /\
      Primops.memory = modexp_memory_footprint m base power res /\
      res = W256.of_int (((W256.to_uint base) ^ (W256.to_uint power)) %% R)
    ] = 1%r.
proof. admit. qed.

lemma modexp_low_pspec_revert :
phoare [ Modexp.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; inline*; wp; by progress. qed.

lemma evaluateLagrangePolyOutOfDomain_low_equiv_mid (memory : mem) (poly256 at256: uint256):
equiv [
    EvaluateLagrangePolyOutOfDomain.low ~ EvaluateLagrangePolyOutOfDomain.mid :
      arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      (
        !Primops.reverted{1} /\
        ((W256.to_uint at256)^DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
        res{2} = Some (to_uint res{1})%W256)
      \/
      (
        Primops.reverted{1} /\
        ((W256.to_uint at256)^DOMAIN_SIZE - 1) %% Constants.R = 0 /\
        res{2} = None
      )
    ].
proof. proc.
    
seq 2 1 : (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  ((poly256 <> W256.zero /\ Primops.memory{1} = (modexp_memory_footprint memory (W256.of_int OMEGA) polyNum{1} omegaPower{1})) 
  \/
  (poly256 = W256.zero /\ Primops.memory{1} = memory)
  )
  /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\ omegaPolyNum{2} = (OMEGA ^ polyNum{2}) %% R
). wp. sp. 
case (bool_of_uint256 polyNum{1}).
(* polyNum != 0 *)
rcondt{1} 1. by progress.
call{1} (modexp_pspec memory (W256.of_int OMEGA) poly256).
skip. progress. left. by auto.
rewrite !W256.of_uintK. have ->: OMEGA %% W256.modulus = OMEGA. by smt(). by reflexivity.
rcondf{1} 1. by progress.
skip. progress. right. by auto.
have ->: polyNum{1} = W256.zero. by smt(). progress. by smt().

seq 1 1: (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  Primops.memory{1} = modexp_memory_footprint memory at{1} (W256.of_int DOMAIN_SIZE) tmp267{1} /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\ omegaPolyNum{2} = (OMEGA ^ polyNum{2}) %% R /\
  tmp267{1} = W256.of_int atDomainSize{2} /\ atDomainSize{2} = (at{2} ^ DOMAIN_SIZE) %% R
).
wp. 
exists* omegaPower{1}. elim* => oP.
pose mem' := (modexp_memory_footprint memory ((of_int OMEGA))%W256 poly256 oP).
case (poly256 = W256.zero).
call{1} (modexp_pspec memory at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt().
rewrite !W256.of_uintK. have ->: DOMAIN_SIZE %% W256.modulus = DOMAIN_SIZE. by smt(). reflexivity.
call{1} (modexp_pspec mem' at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt(). apply modexp_same.
rewrite !W256.of_uintK. have ->: DOMAIN_SIZE %% W256.modulus = DOMAIN_SIZE. by smt(). reflexivity.

seq 1 1: (#pre /\ ret{1} = W256.of_int zd1{2} /\ zd1{2} = (atDomainSize{2} - 1) %% R).
wp. skip. progress.
rewrite /addmod. progress. rewrite !W256.of_uintK !mod_R_W256_mod_R !R_mod_W256_R.
have ->: (R - 1) %% W256.modulus = R - 1. by smt(). by smt.

if. progress.
rewrite /bool_of_uint256 /iszero in H0.
case ((of_int ((to_uint at{1} ^ DOMAIN_SIZE %% R - 1) %% R))%W256 = W256.zero).
progress. by smt.
progress. by smt.
by smt.

seq 1 1: ((to_uint at256 ^ DOMAIN_SIZE - 1) %% R = 0 /\ r{2} = None /\ Primops.reverted{1}).
wp. call{1} revertWithMessage_low_pspec. skip. progress. by smt.
wp. sp. call{1} modexp_low_pspec_revert. skip. progress.

seq 1 1: (
(polyNum{1}, at{1}) = (poly256, at256) /\
(polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
!Primops.reverted{1} /\
Primops.memory{1} = modexp_memory_footprint memory at{1} ((of_int DOMAIN_SIZE))%W256 tmp267{1} /\
omegaPower{1} = (of_int omegaPolyNum{2})%W256 /\ omegaPolyNum{2} = OMEGA ^ polyNum{2} %% R /\
tmp267{1} = (of_int atDomainSize{2})%W256 /\ atDomainSize{2} = at{2} ^ DOMAIN_SIZE %% R /\
ret{1} = (of_int num{2})%W256 /\ num{2} = (omegaPolyNum{2} * zd1{2}) %% R /\
zd1{2} = (atDomainSize{2} - 1) %% R /\ zd1{2} <> 0
).
wp. skip. progress.
rewrite /mulmod. progress. rewrite !W256.of_uintK !mod_R_W256_mod_R !R_mod_W256_R. by smt().
rewrite /bool_of_uint256 /iszero in H0. by smt.

seq 3 1: (
#pre /\ denominator{1} = W256.of_int den{2} /\
den{2} = (DOMAIN_SIZE * (at{2} - omegaPolyNum{2})) %% R
).
wp. skip. progress. 
rewrite /addmod /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: DOMAIN_SIZE %% W256.modulus = DOMAIN_SIZE. by smt().
have ->: (R - OMEGA ^ to_uint polyNum{1} %% R) %% W256.modulus = (R - OMEGA ^ to_uint polyNum{1} %% R). by smt().
have ->: (to_uint at{1} + (R - OMEGA ^ to_uint polyNum{1} %% R)) %% R %% W256.modulus = (to_uint at{1} + (R - OMEGA ^ to_uint polyNum{1} %% R)) %% R. by smt().
by smt().

seq 1 1: (
(polyNum{1}, at{1}) = (poly256, at256) /\
(polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
!Primops.reverted{1} /\
omegaPower{1} = (of_int omegaPolyNum{2})%W256 /\
omegaPolyNum{2} = OMEGA ^ polyNum{2} %% R /\
tmp267{1} = (of_int atDomainSize{2})%W256 /\
atDomainSize{2} = at{2} ^ DOMAIN_SIZE %% R /\
ret{1} = (of_int num{2})%W256 /\
num{2} = omegaPolyNum{2} * zd1{2} %% R /\
zd1{2} = (atDomainSize{2} - 1) %% R /\ zd1{2} <> 0 /\
denominator{1} = (of_int den{2})%W256 /\
den{2} = DOMAIN_SIZE * (at{2} - omegaPolyNum{2}) %% R /\
Primops.memory{1} = modexp_memory_footprint memory at{1} ((W256.of_int R) - (W256.of_int 2)) denominator{1} /\
denominator{1} = W256.of_int inv{2} /\ inv{2} = (den{2} ^ (R - 2)) %% R
).



call (modexp_low_equiv_mid memory (W256.of_int OMEGA) poly256).
skip. progress. by smt. by smt. 
(* polyNum = 0 *)
rcondf{1} 1. by progress.
inline Modexp.mid. wp. skip. progress. by smt.
have ->: polyNum{1} = W256.zero. by smt. progress. by smt.

(* ((poly256 <> W256.zero /\ *)
  (*   Primops.memory{1} = modexp_memory_footprint mem' at{1} (W256.of_int DOMAIN_SIZE) tmp267{1}) \/ *)
  (*  (poly256 = W256.zero /\ *)
  (*    Primops.memory{1} = modexp_memory_footprint memory at{1} (W256.of_int DOMAIN_SIZE) tmp267{1}) *)
  (* ) *)

seq 1 1 : (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\
  Primops.memory{1} = modexp_memory_footprint memory at{1} (W256.of_int DOMAIN_SIZE) tmp267{1} /\
  tmp267{1} = W256.of_int atDomainSize{2}
).

exists* omegaPower{1}. elim* => oP.
pose mem' := (modexp_memory_footprint memory ((of_int OMEGA))%W256 poly256 oP).
case (poly256 = W256.zero).
call (modexp_low_equiv_mid memory at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt. by auto. 
call (modexp_low_equiv_mid mem' at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt. rewrite /mem'. case H0. progress. move => [? ?]. auto. apply modexp_same.

seq 1 1: (#pre /\ ret{1} = W256.of_int zd1{2}). wp. skip. progress.
rewrite /addmod. progress.
rewrite !W256.of_uintK !R_mod_W256_R.  -(modzDm _ (-1) R) modNz. by smt(). by smt().
simplify.

    rewrite (modNz 1).



have ->: (R - 1) %% W256.modulus = R - 1. by smt(). 
have ->: (atDomainSize{2} %% W256.modulus + (R - 1)) = (atDomainSize{2} %% W256.modulus + (R - 1) %% W256.modulus). by smt().

have : forall W256.of_int (a %% R)
have ->: (atDomainSize{2} %% W256.modulus + (R - 1) %% W256.modulus) = (atDomainSize{2} + (R - 1)) %% W256.modulus.  

    rcondf{1} 1. by progress.
inline Modexp.mid. wp. skip. progress. rewrite /bool_of_uint256 in H0. by smt.

