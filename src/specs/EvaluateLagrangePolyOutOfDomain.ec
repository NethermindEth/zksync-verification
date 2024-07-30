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
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module EvaluateLagrangePolyOutOfDomain = {
  proc low(polyNum: uint256, at: uint256): uint256 = {
  var ret, omegaPower, tmp267, _10, denominator;
    omegaPower <- (W256.of_int 1);
    if ((bool_of_uint256 polyNum))
    {
      omegaPower <@ Modexp.low(OMEGA, polyNum);
    }
    
    tmp267 <@ Modexp.low(at, DOMAIN_SIZE);
    ret <- (PurePrimops.addmod tmp267 (R_MOD - W256.one) R_MOD);
    if ((bool_of_uint256 (PurePrimops.iszero ret)))
    {
      RevertWithMessage.low(W256.of_int 28, W256.of_int STRING);
    }
    
    ret <- (PurePrimops.mulmod ret omegaPower R_MOD);
    _10 <- (R_MOD - omegaPower);
    denominator <- (PurePrimops.addmod at _10 R_MOD);
    denominator <- (PurePrimops.mulmod denominator DOMAIN_SIZE R_MOD);
    denominator <@ Modexp.low(denominator, (R_MOD - (W256.of_int 2)));
    ret <- (PurePrimops.mulmod ret denominator R_MOD);
    return ret;
  }
  
  proc mid'(polyNum: int, at: int): int option = {
    var r, omegaPolyNum, atDomainSize, zd1, num, den, inv;

    omegaPolyNum <@ Modexp.mid(OMEGA,polyNum);
    atDomainSize <@ Modexp.mid(at, DOMAIN_SIZE); 

    zd1 <- (atDomainSize - 1) %% R;
    if(zd1 = 0) { (* (at ^ DOMAIN_SIZE) - 1 = 0 *)
      r <- None;
    } else {
      num <- (omegaPolyNum * zd1) %% R;
      den <- (DOMAIN_SIZE * (at - omegaPolyNum)) %% R;
      inv <@ Modexp.mid(den, R - 2);
      r <- Some ((num * inv) %% R);
      (* ((OMEGA ^ polyNum) * (atDomainSize - 1))
        ----------------------------------------
        (DOMAIN_SIZE * (at - (OMEGA ^ polyNum)))
      *)
    }  
    return r;
  }

  proc mid(polyNum: int, at: int): int option = {
    var r, omegaPolyNum, atDomainSize, zd1, num, den, inv;

    omegaPolyNum <- (OMEGA^polyNum) %% R;
    atDomainSize <- (at^DOMAIN_SIZE) %% R; 

    zd1 <- (atDomainSize - 1) %% R;
    if(zd1 = 0) { (* (at ^ DOMAIN_SIZE) - 1 = 0 *)
      r <- None;
    } else {
      num <- (omegaPolyNum * zd1) %% R;
      den <- (DOMAIN_SIZE * (at - omegaPolyNum)) %% R;
      inv <- (den^(R - 2)) %% R;
      r <- Some ((num * inv) %% R);
      (* ((OMEGA ^ polyNum) * (atDomainSize - 1))
        ----------------------------------------
        (DOMAIN_SIZE * (at - (OMEGA ^ polyNum)))
      *)
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
        seq 8 2: (#pre /\ ={tmp267} /\ usr_res{1} = ret{2} /\ _7{1} = PurePrimops.iszero (usr_res{1}) /\ _2{1} = R_MOD /\ _5{1} = DOMAIN_SIZE ).
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

pred lagrange_memory_footprint (initial final : mem)  =
   exists (v1 v2 v3: uint256), final = modexp_memory_footprint initial v1 v2 v3.

lemma evaluateLagrangePolyOutOfDomain_low_equiv_mid' (memory : mem) (poly256 at256: uint256):
equiv [
    EvaluateLagrangePolyOutOfDomain.low ~ EvaluateLagrangePolyOutOfDomain.mid' :
      arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      ((!Primops.reverted{1} /\
        lagrange_memory_footprint memory Primops.memory{1} /\
        res{2} = Some (to_uint res{1})%W256 /\ 0 <= to_uint res{1} < R)
      \/
      (Primops.reverted{1} /\ res{2} = None))
    ].
proof. proc.
    
seq 2 1 : (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  ((poly256 <> W256.zero /\ Primops.memory{1} = (modexp_memory_footprint memory (W256.of_int OMEGA) polyNum{1} omegaPower{1})) 
    \/
  (poly256 = W256.zero /\ Primops.memory{1} = memory))
  /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\ 0 <= omegaPolyNum{2} < R
). sp.
case (bool_of_uint256 polyNum{1}).
(* polyNum != 0 *)
rcondt{1} 1. by progress.
call (modexp_low_equiv_mid memory (W256.of_int OMEGA) poly256).
(* call{1} (modexp_pspec memory (W256.of_int OMEGA) poly256). *)
skip. progress. by smt. left. by auto.
rcondf{1} 1. by progress.
inline Modexp.mid. wp. skip. progress. right. by auto.
have ->: polyNum{1} = W256.zero. by auto. by smt().
have ->: polyNum{1} = W256.zero. by auto. by smt().
have ->: polyNum{1} = W256.zero. by auto. by smt().

seq 1 1: (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  Primops.memory{1} = modexp_memory_footprint memory at{1} (W256.of_int DOMAIN_SIZE) tmp267{1} /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\ 0 <= omegaPolyNum{2} < R /\
  tmp267{1} = W256.of_int atDomainSize{2} /\ 0 <= atDomainSize{2} < R
).
wp. 
exists* omegaPower{1}. elim* => oP.
pose mem' := (modexp_memory_footprint memory ((of_int OMEGA))%W256 poly256 oP).
case (poly256 = W256.zero).
call{1} (modexp_low_equiv_mid memory at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt. by smt().
call{1} (modexp_low_equiv_mid mem' at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt. by smt(). apply modexp_memory_footprint_same.

seq 1 1: (#pre /\ ret{1} = W256.of_int zd1{2} /\ 0 <= zd1{2} < R).
wp. skip. progress.
rewrite /addmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: (R - 1) %% W256.modulus = R - 1. by smt().
have ->: atDomainSize{2} %% W256.modulus = atDomainSize{2}. by smt().
by smt(). by smt(). by smt().

if. progress. by smt. by smt.

seq 1 1: (r{2} = None /\ Primops.reverted{1}).
wp. call{1} revertWithMessage_low_pspec. skip. by progress.
wp. sp. call{1} modexp_low_pspec_revert. skip. by progress.

seq 1 1: (
(polyNum{1}, at{1}) = (poly256, at256) /\
(polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
!Primops.reverted{1} /\
Primops.memory{1} = modexp_memory_footprint memory at{1} ((of_int DOMAIN_SIZE))%W256 tmp267{1} /\
omegaPower{1} = (of_int omegaPolyNum{2})%W256 /\ 0 <= omegaPolyNum{2} < R /\
tmp267{1} = (of_int atDomainSize{2})%W256 /\ 0 <= atDomainSize{2} < R /\ 0 <= zd1{2} < R /\
ret{1} = (of_int num{2})%W256 /\ 0 <= num{2} < R
).
wp. skip. progress.
rewrite /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: zd1{2} %% W256.modulus = zd1{2}. by smt().
have ->: omegaPolyNum{2} %% W256.modulus = omegaPolyNum{2}. by smt().
by smt(). by smt(). by smt().

seq 3 1: (
#pre /\ denominator{1} = W256.of_int den{2} /\ 0 <= den{2} < R
).
wp. skip. progress. 
rewrite /addmod /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: DOMAIN_SIZE %% W256.modulus = DOMAIN_SIZE. by smt().
have ->: (R - omegaPolyNum{2}) %% W256.modulus = (R - omegaPolyNum{2}). by smt().
rewrite !mod_R_W256_mod_R. by smt. by smt(). by smt().

seq 1 1: (
(polyNum{1}, at{1}) = (poly256, at256) /\
(polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
!Primops.reverted{1} /\
omegaPower{1} = (of_int omegaPolyNum{2})%W256 /\
0 <= omegaPolyNum{2} < R /\
tmp267{1} = (of_int atDomainSize{2})%W256 /\
0 <= atDomainSize{2} < R /\
ret{1} = (of_int num{2})%W256 /\
0 <= num{2} < R /\ 0 <= zd1{2} < R /\ 0 <= den{2} < R /\
Primops.memory{1} = modexp_memory_footprint memory (of_int den{2})%W256 (W256.of_int (R - 2)) denominator{1} /\
denominator{1} = W256.of_int inv{2} /\ 0 <= inv{2} < R
).

exists* tmp267{1}. elim* => tmp. exists* denominator{1}. elim* => d.
pose mem' := modexp_memory_footprint memory at256 ((of_int DOMAIN_SIZE))%W256 tmp.
call{1} (modexp_low_equiv_mid mem' d ((W256.of_int R) - (W256.of_int 2))).
skip. progress. rewrite /mem'. by smt. by smt. apply modexp_memory_footprint_same.
wp. skip. progress. rewrite /lagrange_memory_footprint. by smt().
rewrite /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: num{2} %% W256.modulus = num{2}. by smt().
have ->: inv{2} %% W256.modulus = inv{2}. by smt().
rewrite mod_R_W256_mod_R. by reflexivity.
rewrite /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: num{2} %% W256.modulus = num{2}. by smt().
have ->: inv{2} %% W256.modulus = inv{2}. by smt().
rewrite mod_R_W256_mod_R. by smt().
rewrite /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: num{2} %% W256.modulus = num{2}. by smt().
have ->: inv{2} %% W256.modulus = inv{2}. by smt().
rewrite mod_R_W256_mod_R. by smt().
qed.

lemma evaluateLagrangePolyOutOfDomain_low_equiv_mid (memory : mem) (poly256 at256: uint256):
equiv [
    EvaluateLagrangePolyOutOfDomain.low ~ EvaluateLagrangePolyOutOfDomain.mid :
      arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      ((!Primops.reverted{1} /\ ((to_uint at256)^DOMAIN_SIZE - 1) %% R <> 0 /\
        lagrange_memory_footprint memory Primops.memory{1} /\
        res{2} = Some (to_uint res{1})%W256 /\ 0 <= to_uint res{1} < R)
      \/
      (Primops.reverted{1} /\ ((to_uint at256)^DOMAIN_SIZE - 1) %% R = 0 /\ res{2} = None))
    ].
proof.
transitivity EvaluateLagrangePolyOutOfDomain.mid'
(
arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      ((!Primops.reverted{1} /\
        lagrange_memory_footprint memory Primops.memory{1} /\
        res{2} = Some (to_uint res{1})%W256 /\ 0 <= to_uint res{1} < R)
      \/
      (Primops.reverted{1} /\ res{2} = None))
)
(
arg{1} = (to_uint poly256, to_uint at256)%W256 /\ ={arg}
      ==>
      ={res} /\
      ((((to_uint at256)^DOMAIN_SIZE - 1) %% R <> 0 /\ is_some res{2})
      \/
      (((to_uint at256)^DOMAIN_SIZE - 1) %% R = 0 /\ !(is_some res{2})))
).
progress. exists (to_uint poly256, to_uint at256). by progress.
progress. elim H0. progress. by smt(). by smt().
apply evaluateLagrangePolyOutOfDomain_low_equiv_mid'.
proc. inline Modexp.mid. wp. skip. progress. by smt(). by smt(). qed.
