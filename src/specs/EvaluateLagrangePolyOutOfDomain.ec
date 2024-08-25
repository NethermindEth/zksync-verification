pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
require        Constants.
require import Field.
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

    omegaPolyNum <@ Modexp.mid(Constants.OMEGA,polyNum);
    atDomainSize <@ Modexp.mid(at, Constants.DOMAIN_SIZE); 

    zd1 <- (atDomainSize - 1) %% Constants.R;
    if(zd1 = 0) { (* (at ^ DOMAIN_SIZE) - 1 = 0 *)
      r <- None;
    } else {
      num <- (omegaPolyNum * zd1) %% Constants.R;
      den <- (Constants.DOMAIN_SIZE * (at - omegaPolyNum)) %% Constants.R;
      inv <@ Modexp.mid(den, Constants.R - 2);
      r <- Some ((num * inv) %% Constants.R);
      (* ((OMEGA ^ polyNum) * (atDomainSize - 1))
        ----------------------------------------
        (DOMAIN_SIZE * (at - (OMEGA ^ polyNum)))
      *)
    }  
    return r;
  }

  proc mid(polyNum: int, at: int): int option = {
    var r, omegaPolyNum, atDomainSize, zd1, num, den, inv;

    omegaPolyNum <- (Constants.OMEGA^polyNum) %% Constants.R;
    atDomainSize <- (at^Constants.DOMAIN_SIZE) %% Constants.R; 

    zd1 <- (atDomainSize - 1) %% Constants.R;
    if(zd1 = 0) { (* (at ^ DOMAIN_SIZE) - 1 = 0 *)
      r <- None;
    } else {
      num <- (omegaPolyNum * zd1) %% Constants.R;
      den <- (Constants.DOMAIN_SIZE * (at - omegaPolyNum)) %% Constants.R;
      inv <- (den^(Constants.R - 2)) %% Constants.R;
      r <- Some ((num * inv) %% Constants.R);
      (* ((OMEGA ^ polyNum) * (atDomainSize - 1))
        ----------------------------------------
        (DOMAIN_SIZE * (at - (OMEGA ^ polyNum)))
      *)
    }  
    return r;
  }

  proc high(polyNum: int, at: FieldR.F): FieldR.F option = {
      var r, omegaPolyNum, atDomainSize, zd1;

      omegaPolyNum <- Constants.OMEGAFr ^ polyNum;
      atDomainSize <- at^Constants.DOMAIN_SIZE;

      zd1 <-FieldR.(-) atDomainSize (FieldR.inF 1);

      if (zd1 = FieldR.zero) {
        r <- None;
      } else {
        r <- Some (FieldR.( * ) (FieldR.( * ) omegaPolyNum zd1) (FieldR.( * ) Constants.DOMAIN_SIZEFr (FieldR.(-) at omegaPolyNum) ^ (- 1)));
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
        call modexp_extracted_equiv_low. skip. by progress.
      (* case !bool_of_uint256 polyNum{2}). *)
        rcondf{1} 1. by progress.
        rcondf{2} 1. by progress.
        skip. by progress.
      (* finished seq 2 2 *)
        wp.
        call modexp_extracted_equiv_low.
        seq 8 2: (#pre /\ ={tmp267} /\ usr_res{1} = ret{2} /\ _7{1} = PurePrimops.iszero (usr_res{1}) /\ _2{1} = R_MOD /\ _5{1} = DOMAIN_SIZE ).
        wp. sp.
        call modexp_extracted_equiv_low. skip. by progress.
      (* finished seq 8 2 *)
        if. by progress.
        sp.
        wp.
        call revertWithMessage_extracted_equiv_low. skip. by progress.
        sp. skip. by progress.
    qed.

lemma evaluateLagrangePolyOutOfDomain_pspec_revert :
phoare [ EvaluateLagrangePolyOutOfDomain.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; inline*; wp; skip; by auto. qed.

op lagrange_memory_footprint (m : mem) (v1 v2 v3 : uint256)  =
   modexp_memory_footprint m v1 v2 v3.

lemma evaluateLagrangePolyOutOfDomain_low_equiv_mid' (memory : mem) (poly256 at256: uint256):
equiv [
    EvaluateLagrangePolyOutOfDomain.low ~ EvaluateLagrangePolyOutOfDomain.mid' :
      arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      ((!Primops.reverted{1} /\
        exists (v1 v2 v3: uint256), Primops.memory{1} = lagrange_memory_footprint memory v1 v2 v3 /\
        res{2} = Some (to_uint res{1})%W256 /\ 0 <= to_uint res{1} < Constants.R)
      \/
      (Primops.reverted{1} /\ res{2} = None))
    ].
proof. proc.
    
seq 2 1 : (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  ((poly256 <> W256.zero /\ Primops.memory{1} = (modexp_memory_footprint memory (W256.of_int Constants.OMEGA) polyNum{1} omegaPower{1})) 
    \/
  (poly256 = W256.zero /\ Primops.memory{1} = memory))
  /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\ 0 <= omegaPolyNum{2} < Constants.R
). sp.
case (bool_of_uint256 polyNum{1}).
(* polyNum != 0 *)
rcondt{1} 1. by progress.
call (modexp_low_equiv_mid memory (W256.of_int Constants.OMEGA) poly256).
(* call{1} (modexp_pspec memory (W256.of_int OMEGA) poly256). *)
skip. progress.
rewrite Constants.OMEGA_int. rewrite W256.to_uintK. reflexivity.
rewrite W256.of_uintK. rewrite pmod_small. rewrite /Constants.OMEGA. trivial.  reflexivity.
left. by auto.
rcondf{1} 1. by progress.
inline Modexp.mid. wp. skip. progress. right. by auto.
have ->: polyNum{1} = W256.zero. by auto. by smt().
have ->: polyNum{1} = W256.zero. by auto. by smt().
have ->: polyNum{1} = W256.zero. by auto. by smt().

seq 1 1: (
  (polyNum{1}, at{1}) = (poly256, at256) /\
  (polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
  !Primops.reverted{1} /\
  Primops.memory{1} = modexp_memory_footprint memory at{1} (W256.of_int Constants.DOMAIN_SIZE) tmp267{1} /\
  omegaPower{1} = W256.of_int omegaPolyNum{2} /\ 0 <= omegaPolyNum{2} < Constants.R /\
  tmp267{1} = W256.of_int atDomainSize{2} /\ 0 <= atDomainSize{2} < Constants.R
).
wp. 
exists* omegaPower{1}. elim* => oP.
pose mem' := (modexp_memory_footprint memory ((of_int Constants.OMEGA))%W256 poly256 oP).
case (poly256 = W256.zero).
call{1} (modexp_low_equiv_mid memory at256 (W256.of_int Constants.DOMAIN_SIZE)).
skip. progress. rewrite /DOMAIN_SIZE /Constants.DOMAIN_SIZE. reflexivity.
rewrite /DOMAIN_SIZE /Constants.DOMAIN_SIZE. rewrite W256.of_uintK. rewrite pmod_small. trivial. reflexivity.
smt ().
call{1} (modexp_low_equiv_mid mem' at256 (W256.of_int Constants.DOMAIN_SIZE)).
skip. progress.
rewrite /DOMAIN_SIZE /Constants.DOMAIN_SIZE. reflexivity.
rewrite W256.of_uintK. rewrite pmod_small /Constants.DOMAIN_SIZE. trivial. reflexivity.
smt ().
apply modexp_memory_footprint_same.

seq 1 1: (#pre /\ ret{1} = W256.of_int zd1{2} /\ 0 <= zd1{2} < Constants.R).
wp. skip. progress.
rewrite /addmod. progress. rewrite !W256.of_uintK. rewrite - /Constants.R.
have ->: atDomainSize{2} %% W256.modulus = atDomainSize{2}. by smt().
have ->: to_uint (R_MOD - W256.one) = Constants.R - 1. by smt (@W256 @Utils).

by smt(). by smt(). by smt().

if. progress. by smt. rewrite /iszero /bool_of_uint256. smt (@W256 @Utils).

seq 1 1: (r{2} = None /\ Primops.reverted{1}).
wp. call{1} revertWithMessage_low_pspec. skip. by progress.
wp. sp. call{1} modexp_low_pspec_revert. skip. by progress.

seq 1 1: (
(polyNum{1}, at{1}) = (poly256, at256) /\
(polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
!Primops.reverted{1} /\
Primops.memory{1} = modexp_memory_footprint memory at{1} ((of_int Constants.DOMAIN_SIZE))%W256 tmp267{1} /\
omegaPower{1} = (of_int omegaPolyNum{2})%W256 /\ 0 <= omegaPolyNum{2} < Constants.R /\
tmp267{1} = (of_int atDomainSize{2})%W256 /\ 0 <= atDomainSize{2} < Constants.R /\ 0 <= zd1{2} < Constants.R /\
ret{1} = (of_int num{2})%W256 /\ 0 <= num{2} < Constants.R
).
wp. skip. progress.
rewrite /mulmod. progress. rewrite !W256.of_uintK. rewrite - /Constants.R.
have ->: zd1{2} %% W256.modulus = zd1{2}. by smt().
have ->: omegaPolyNum{2} %% W256.modulus = omegaPolyNum{2}. by smt().
by smt(). by smt(). by smt().

seq 3 1: (
#pre /\ denominator{1} = W256.of_int den{2} /\ 0 <= den{2} < Constants.R
).
wp. skip. progress. 
rewrite /addmod /mulmod. progress. rewrite !W256.of_uintK. rewrite - /Constants.R.
do (rewrite (pmod_small _ W256.modulus); first smt (@W256 @IntDiv @Utils)).
rewrite / Constants.DOMAIN_SIZE.
congr. rewrite mulrC.
    have ->: (W256.to_uint at{1} + W256.to_uint (R_MOD - (W256.of_int omegaPolyNum{2}))) %% Constants.R = (W256.to_uint at{1} - omegaPolyNum{2}) %% Constants.R.
      rewrite - modzDmr.
      have ->: W256.to_uint (R_MOD - (W256.of_int omegaPolyNum{2})) %% Constants.R = (- omegaPolyNum{2}) %% Constants.R.
    rewrite uint256_cast_sub. rewrite - Constants.R_int. do rewrite W256.of_uintK.
    rewrite (pmod_small _ W256.modulus). smt (@IntDiv). rewrite (pmod_small _ W256.modulus). smt (@IntDiv).
    rewrite (pmod_small _ W256.modulus). smt (). smt (@IntDiv). smt (@IntDiv).
    smt (@IntDiv). smt (). smt ().

seq 1 1: (
(polyNum{1}, at{1}) = (poly256, at256) /\
(polyNum{2}, at{2}) = (to_uint poly256, to_uint at256) /\
!Primops.reverted{1} /\
omegaPower{1} = (of_int omegaPolyNum{2})%W256 /\
0 <= omegaPolyNum{2} < Constants.R /\
tmp267{1} = (of_int atDomainSize{2})%W256 /\
0 <= atDomainSize{2} < Constants.R /\
ret{1} = (of_int num{2})%W256 /\
0 <= num{2} < Constants.R /\ 0 <= zd1{2} < Constants.R /\ 0 <= den{2} < Constants.R /\
Primops.memory{1} = modexp_memory_footprint memory (of_int den{2})%W256 (W256.of_int (Constants.R - 2)) denominator{1} /\
denominator{1} = W256.of_int inv{2} /\ 0 <= inv{2} < Constants.R
).

exists* tmp267{1}. elim* => tmp. exists* denominator{1}. elim* => d.
pose mem' := modexp_memory_footprint memory at256 ((of_int Constants.DOMAIN_SIZE))%W256 tmp.
call{1} (modexp_low_equiv_mid mem' d ((W256.of_int Constants.R) - (W256.of_int 2))).
skip. progress. rewrite /mem'. by smt. by smt. smt (@Constants @W256 @Utils). apply modexp_memory_footprint_same.
wp. skip. progress.
exists (of_int den{2})%W256 (of_int (Constants.R - 2))%W256 (of_int inv{2})%W256. progress.
rewrite /mulmod. progress. rewrite !W256.of_uintK.
do 4! (rewrite (pmod_small _ W256.modulus); first smt (@IntDiv)).
rewrite /Constants.R. reflexivity. smt (@W256).
    rewrite /mulmod. progress.
    rewrite W256.of_uintK.
rewrite - Constants.R_int. rewrite (pmod_small _ W256.modulus). smt (@IntDiv). smt (@IntDiv).
qed.

lemma evaluateLagrangePolyOutOfDomain_low_equiv_mid (memory : mem) (poly256 at256: uint256):
equiv [
    EvaluateLagrangePolyOutOfDomain.low ~ EvaluateLagrangePolyOutOfDomain.mid :
      arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      ((!Primops.reverted{1} /\ ((to_uint at256)^Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\
        exists (v1 v2 v3: uint256), Primops.memory{1} = lagrange_memory_footprint memory v1 v2 v3 /\
        res{2} = Some (to_uint res{1})%W256 /\ 0 <= to_uint res{1} < Constants.R)
      \/
      (Primops.reverted{1} /\ ((to_uint at256)^Constants.DOMAIN_SIZE - 1) %% Constants.R = 0 /\ res{2} = None))
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
        exists (v1 v2 v3: uint256), Primops.memory{1} = lagrange_memory_footprint memory v1 v2 v3 /\
        res{2} = Some (to_uint res{1})%W256 /\ 0 <= to_uint res{1} < Constants.R)
      \/
      (Primops.reverted{1} /\ res{2} = None))
)
(
arg{1} = (to_uint poly256, to_uint at256)%W256 /\ ={arg}
      ==>
      ={res} /\
      ((((to_uint at256)^Constants.DOMAIN_SIZE - 1) %% Constants.R <> 0 /\ is_some res{2})
      \/
      (((to_uint at256)^Constants.DOMAIN_SIZE - 1) %% Constants.R = 0 /\ !(is_some res{2})))
).
progress. exists (to_uint poly256, to_uint at256). by progress.
progress. elim H0. progress. by smt(). by smt().
apply evaluateLagrangePolyOutOfDomain_low_equiv_mid'.
proc. inline Modexp.mid. wp. skip. progress. by smt(). by smt(). qed.

lemma lagrange (x: FieldR.F) : x ^ Constants.DOMAIN_SIZE <> FieldR.one => forall (n: int), x <> Constants.OMEGAFr ^ n. 
proof. admit. qed.
    
lemma evaluateLagrangePolyOutOfDomain_mid_equiv_high (memory : mem) (polyInt: int) (atF: FieldR.F):
equiv [
    EvaluateLagrangePolyOutOfDomain.mid ~ EvaluateLagrangePolyOutOfDomain.high :
      0 <= polyInt /\
      arg{1} = (polyInt, FieldR.asint atF) /\
      arg{2} = (polyInt, atF) 
      ==>
      omap FieldR.inF res{1} = res{2}
    ].
proof.
  proc.
  seq 3 3: (#pre /\ FieldR.inF omegaPolyNum{1} = omegaPolyNum{2} /\ FieldR.inF atDomainSize{1} = atDomainSize{2} /\ FieldR.inF zd1{1} = zd1{2} /\ zd1{1} = zd1{1} %% FieldR.p
           /\ zd1{2} = FieldR.( - ) (at{2} ^ Constants.DOMAIN_SIZE) FieldR.one /\ omegaPolyNum{2} = Constants.OMEGAFr ^ polyNum{2}).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p -FieldR.inF_mod FieldR.inF_exp -Constants.omega_eq_omegaFr H FieldR.asintK /( ^ ); by progress.
  rewrite Constants.r_eq_fieldr_p -FieldR.inF_mod FieldR.inF_exp /Constants.DOMAIN_SIZE FieldR.asintK /(^); by progress.
  rewrite Constants.r_eq_fieldr_p FieldR.inFB_mod -FieldR.inF_mod FieldR.inF_exp /Constants.DOMAIN_SIZE /(^) FieldR.asintK; by progress. 
  rewrite -Constants.r_eq_fieldr_p. rewrite IntDiv.modz_mod; by reflexivity. 
  case (zd1{1} = 0).
  if; progress; do! (wp; skip; progress); progress. 
  if. progress.
  rewrite H0 -FieldR.inFK.
  search FieldR.asint.
  rewrite -FieldR.zeroE.
  congr.
  wp. skip. progress. 
  seq 1 0: (#pre /\ FieldR.inF num{1} = FieldR.( * ) omegaPolyNum{2} zd1{2}).  
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p -FieldR.inF_mod FieldR.inFM; by reflexivity. 
  seq 1 0: (#pre /\ FieldR.inF den{1} = FieldR.( * ) Constants.DOMAIN_SIZEFr (FieldR.( - ) atF omegaPolyNum{2}) ).
  wp. skip. progress.
  rewrite Constants.r_eq_fieldr_p -FieldR.inF_mod FieldR.inFM FieldR.inFB FieldR.asintK /DOMAIN_SIZEFr; by reflexivity.
  seq 1 0: (#pre /\ FieldR.inF inv{1} = (FieldR.( * ) Constants.DOMAIN_SIZEFr (FieldR.( - ) atF omegaPolyNum{2})) ^ (-1) ).  
  wp. skip. progress. 
  rewrite Constants.r_eq_fieldr_p -FieldR.inF_mod. 
  rewrite FieldR.inF_exp -Constants.r_eq_fieldr_p /Constants.R; progress.
  have -> : 21888242871839275222246405745257275088548364400416034343698204186575808495615 = Constants.R - 2 by rewrite /Constants.R; progress.
  rewrite Constants.r_eq_fieldr_p -FieldR.inv_exp_sub_p_2.
  have HHH : forall (n: int), at{2} <> Constants.OMEGAFr ^ n. apply lagrange.
  have blu: (FieldR.( - ) (at{2} ^ Constants.DOMAIN_SIZE) FieldR.one) <> FieldR.zero. by smt (@FieldR). 
  by smt (@FieldR).
  rewrite H6 FieldR.ZrRing.unitrMr FieldR.unitE /DOMAIN_SIZEFr /Constants.DOMAIN_SIZE. have -> : FieldR.zero = FieldR.inF 0 by smt(@FieldR).
  rewrite -FieldR.eq_inF -Constants.r_eq_fieldr_p /Constants.R; by progress.
  rewrite H2.
  by smt (@FieldR).
  by smt (@FieldR).
  wp. skip. progress. 
  rewrite Constants.r_eq_fieldr_p FieldR.inFM_mod.
  congr.
qed. 
