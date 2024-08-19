pragma Goals:printall.

require import AllCore.
require        Constants.
require import Field.
require import Int.
require import IntDiv.
require import Memory.
require import PurePrimops.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import Verifier.
require import VerifierConsts.
require import YulPrimops.

import MemoryMap.

module PointNegate = {
  proc low(usr_point : uint256): unit = {
    var _2, usr_pY, tmp90, tmp91, _6, _7 : uint256;
    _2 <- (usr_point + W256.of_int 32);
    usr_pY <@ Primops.mload(_2);
    if (usr_pY = W256.zero) {
      tmp90 <@ Primops.mload(usr_point);
      if (bool_of_uint256 tmp90) {
        RevertWithMessage.low((W256.of_int 26), W256.of_int STRING);
      }
    }
    else {
      Primops.mstore(_2, (Q_MOD - usr_pY));
    }
  }

  proc mid(point: int*int) : (int * int) option = {
    var ret;
    if (point.`1 <> 0 /\ point.`2 = 0) {
      ret <- None;
    } else {
      ret <- Some (point.`1, (-point.`2) %% Constants.Q);
    }
    return ret;
  }

  proc high_field(p: FieldQ.F*FieldQ.F) : (FieldQ.F*FieldQ.F) option = {
    var ret: (FieldQ.F*FieldQ.F) option;
    if (p.`1 <> FieldQ.zero /\ p.`2 = FieldQ.zero) {
      ret <- None;
    } else {
      ret <- Some (p.`1, -p.`2);
    }
    return ret;
  }
}.

lemma pointNegate_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_pointNegate ~ PointNegate.low :
      ={arg, glob PointNegate} ==>
      ={res, glob PointNegate}
    ].
    proof.
      proc.
      seq 4  2 : (#pre /\ ={usr_pY, _2}).
      inline*. wp. skip. by progress.
      sp.
      if. by progress.
      seq 1 1: (#pre /\ ={tmp90}).
      inline*. wp. skip. by progress.
      sp.
      if. by progress.
      sp.
      call revertWithMessage_extracted_equiv_low.
      skip. by progress.
      skip. by progress.
      inline*. wp. skip. rewrite /Constants.Q. by progress.
    qed.

lemma aux (x : int): 0 < x => x < Constants.Q => (-x) %% Constants.Q = Constants.Q - x.
proof. progress. rewrite -modzDl pmod_small. split. smt ().
progress.  smt (). reflexivity. qed.
    
lemma pointNegate_low_equiv_mid (memory: mem) (point_address: uint256) (point_x_int point_y_int: int):
    equiv [
      PointNegate.low ~ PointNegate.mid :
      arg{2} = (point_x_int, point_y_int) /\
      arg{1} = point_address /\
      point_x_int < Constants.Q /\
      point_y_int < Constants.Q /\
      Primops.memory{1} = memory /\
      W256.to_uint(PurePrimops.mload memory point_address) = point_x_int /\
      W256.to_uint(PurePrimops.mload memory (point_address + W256.of_int 32)) = point_y_int /\
      !Primops.reverted{1}
      ==>
      (
        (res{2} = None /\ Primops.reverted{1}) \/
        (exists (p: int*int),
          0 <= p.`1 < Constants.Q /\ 0 <= p.`2 < Constants.Q /\
          res{2} = Some p /\
          !Primops.reverted{1} /\
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory point_address (W256.of_int p.`1)) (point_address + W256.of_int 32) (W256.of_int p.`2)
        )
     )
   ].
   proof. proc.
     inline Primops.mload Primops.mstore.
     (* case (point{2}.`1 = 0).
     case (point{2}.`2 = 0).
     rcondt{1} 4. progress. wp. skip. progress. smt (@W256).
     rcondf{1} 6. progress. wp. skip. progress. smt (@W256).
     rcondf{2} 1. progress. skip. progress. smt (@W256).
     sp. skip. progress. rewrite H1 H2. exists (0,0). progress.
     have H_x: W256.zero = load Primops.memory{1} usr_point{1} by smt(@W256).
     have H_y: W256.zero = load Primops.memory{1} (usr_point{1} + W256.of_int 32) by smt(@W256). *)

   
     case (point_x_int <> 0 /\ point_y_int = 0).
     rcondt{2} 1. by progress.
     sp. rcondt{1} 1. progress. skip. progress. rewrite - W256.to_uintK.
     rewrite H3. reflexivity.
     sp. rcondt{1} 1. progress. skip. progress. rewrite /bool_of_uint256.
     rewrite - W256.to_uintK. smt(@W256).
     call{1} (revertWithMessage_low_pspec).
     skip. by progress.
     rcondf{2} 1. by progress.
     case (point_y_int = 0).
     rcondt{1} 4. progress. sp. skip. progress. rewrite - W256.to_uintK. rewrite H3. reflexivity.
     sp. rcondf{1} 1. progress. skip. progress. smt (@W256).
     skip. progress. rewrite H3. simplify.
     exists (W256.to_uint (load Primops.memory{1} usr_point{1}), 0).
     progress.
     smt (@W256 @Utils). smt (@Constants).
     rewrite - H3. rewrite W256.to_uintK.
     rewrite MemoryMap.store_loaded_val.
     rewrite MemoryMap.store_loaded_val.
     reflexivity.
     sp. rcondf{1} 1. progress. skip. progress. smt(@W256).
     sp. skip. progress.
     exists (W256.to_uint (load memory usr_point{1}), (- W256.to_uint (load memory (usr_point{1} + (W256.of_int 32)))) %% Constants.Q).
     progress. smt (@W256 @Utils). smt (@W256 @Utils). smt (@IntDiv).
     congr. rewrite MemoryMap.store_loaded_val. reflexivity.
     pose y := load memory (usr_point{1} + W256.of_int 32).
     rewrite aux.
     smt (@W256).
     smt ().
     smt (@W256).
qed.

lemma pointNegate_mid_equiv_high_field:
equiv [
    PointNegate.mid ~ PointNegate.high_field:
      point{1} = F_to_int_point p{2} ==>
      (
        (res{1} = None /\ res{2} = None) \/
        (exists (ret_int: int*int, ret_f: FieldQ.F*FieldQ.F),
          res{1} = Some ret_int /\ res{2} = Some ret_f /\
          ret_int = F_to_int_point ret_f
        )
      )
    ].
    proof.
      proc.
      wp. skip.
      progress.
      smt (@EllipticCurve).
      smt (@EllipticCurve).
      smt (@EllipticCurve).
      exists (F_to_int_point (p{2}.`1, (-p{2}.`2)%FieldQ)).
      exists (p{2}.`1, (-p{2}.`2)%FieldQ).
      progress.
      rewrite Constants.q_eq_fieldq_p.
      rewrite /F_to_int_point. simplify.
      rewrite FieldQ.oppE.
      reflexivity.
    qed.


      
    
