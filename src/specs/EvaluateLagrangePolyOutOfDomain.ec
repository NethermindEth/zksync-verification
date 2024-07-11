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

  proc low'(polyNum: uint256, at: uint256): uint256 = {
  var ret, omegaPower, tmp267, _10, denominator;
    tmp267 <@ Modexp.low(at, (W256.of_int Constants.DOMAIN_SIZE));

    omegaPower <- (W256.of_int 1);
    if ((bool_of_uint256 polyNum))
    {
      omegaPower <@ Modexp.low((W256.of_int Constants.OMEGA), polyNum);
    }
    
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
  
  proc mid(polyNum: int, at: int): int option = {
    var r, omegaP, zd1, num, den, inv;

    omegaP <@ Modexp.mid(OMEGA, polyNum);
    zd1 <- (at^DOMAIN_SIZE - 1) %% R;
    
    if(zd1 = 0) {
      r <- None;
    } else {
      num <- (omegaP * zd1) %% R;
      den <- (DOMAIN_SIZE * (at - omegaP)) %% R;
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

lemma evaluateLagrangePolyOutOfDomain_low_equiv_mid (memory : mem) (poly256 at256 r: uint256):
equiv [
    EvaluateLagrangePolyOutOfDomain.low ~ EvaluateLagrangePolyOutOfDomain.mid :
      arg{1} = (poly256, at256) /\
      arg{2} = (to_uint poly256, to_uint at256)%W256 /\
      !Primops.reverted{1} /\
      Primops.memory{1} = memory
      ==>
      (
        !Primops.reverted{1} /\
        res{2} = Some (to_uint res{1})%W256)
      \/
      (
        Primops.reverted{1} /\
        ((W256.to_uint at256)^DOMAIN_SIZE - 1) %% Constants.R = 0 /\
        res{2} = None
      )
    ].
proof. proc.
seq 2 1 : (#pre /\ omegaPower{1} = W256.of_int omegaP{2}).
seq 1 0 : (#pre /\ omegaPower{1} = W256.one). wp. skip. auto.
case (bool_of_uint256 polyNum{1}).
rcondt{1} 1. by progress.
call (modexp_low_equiv_mid memory (W256.of_int OMEGA) poly256).
skip. progress. smt. admit. (* HERE *)
rcondf{1} 1. by progress.
inline Modexp.mid. wp. skip. progress. rewrite /bool_of_uint256 in H0. by smt.

