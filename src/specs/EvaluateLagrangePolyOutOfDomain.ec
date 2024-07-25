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

(* lemma modexp_pspec (m : mem) (base power : uint256) : *)
(*     phoare [ Modexp.low : *)
(*       arg = (base, power) /\ *)
(*       Primops.memory = m /\ *)
(*       !Primops.reverted *)
(*       ==> *)
(*       !Primops.reverted /\ *)
(*       Primops.memory = modexp_memory_footprint m base power res /\ *)
(*       res = W256.of_int (((W256.to_uint base) ^ (W256.to_uint power)) %% R) *)
(*     ] = 1%r. *)
(* proof. admit. qed. *)

lemma modexp_low_equiv_mid_test (memory: mem) (value256 power256: uint256):
    equiv [
      Modexp.low ~ Modexp.mid:
      arg{1} = (value256, power256) /\
      arg{2} = (W256.to_uint value256, W256.to_uint power256) /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory    
      ==>
      res{2} = W256.to_uint res{1} /\
      !Primops.reverted{1} /\
      0 <= res{2} < R /\
      Primops.memory{1} = (modexp_memory_footprint memory value256 power256 res{1})
    ].
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
      (!Primops.reverted{1} /\ res{2} = Some (to_uint res{1})%W256)
      \/
      (Primops.reverted{1} /\ res{2} = None)
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
call (modexp_low_equiv_mid_test memory (W256.of_int OMEGA) poly256).
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
call{1} (modexp_low_equiv_mid_test memory at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt. by smt().
call{1} (modexp_low_equiv_mid_test mem' at256 (W256.of_int DOMAIN_SIZE)).
skip. progress. by smt. by smt(). apply modexp_same.

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
0 <= num{2} < R /\
0 <= zd1{2} < R /\
0 <= den{2} < R /\
Primops.memory{1} = modexp_memory_footprint memory (of_int den{2})%W256 (W256.of_int (R - 2)) denominator{1} /\
denominator{1} = W256.of_int inv{2} /\ 0 <= inv{2} < R
).

exists* tmp267{1}. elim* => tmp. exists* denominator{1}. elim* => d.
pose mem' := modexp_memory_footprint memory at256 ((of_int DOMAIN_SIZE))%W256 tmp.
call{1} (modexp_low_equiv_mid_test mem' d ((W256.of_int R) - (W256.of_int 2))).
skip. progress. rewrite /mem'. by smt. by smt. apply modexp_same.
wp. skip. progress. rewrite /mulmod. progress. rewrite !W256.of_uintK !R_mod_W256_R.
have ->: num{2} %% W256.modulus = num{2}. by smt().
have ->: inv{2} %% W256.modulus = inv{2}. by smt().
rewrite mod_R_W256_mod_R. by reflexivity.
qed.

lemma lagrange_pspec_mid (polyNum at: int) :
    phoare [ EvaluateLagrangePolyOutOfDomain.mid :
      arg = (polyNum, at)
      ==>
      let opR = OMEGA ^ polyNum %% R in
      let aDR = (at ^ DOMAIN_SIZE %% R - 1) %% R in
      let inv = (DOMAIN_SIZE * (at - opR) %% R) ^ (R - 2) %% R in
      ((at^DOMAIN_SIZE - 1) %% Constants.R <> 0 /\ res = Some ((opR * aDR) * inv %% R))
        \/
      ((at^DOMAIN_SIZE - 1) %% Constants.R = 0 /\ res = None)
    ] = 1%r.
proof. proc.
inline Modexp.mid; wp; skip. progress; by smt(). 
qed.
