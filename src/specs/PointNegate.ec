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

import FieldQ.
import MemoryMap.

type Point = F * F.

pred IsPointValid (point: Point) =
  !(point.`1 <> FieldQ.zero /\ point.`2 = FieldQ.zero).

(* High *)
op pointNegate (point: Point): Point option =
  if !IsPointValid point then None else Some (point.`1, -(point.`2)).

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

  proc mid(point_x: int, point_y: int) : int * int = {
    var ret_x, ret_y;
    ret_x <- point_x;
    ret_y <- point_y;
    if (point_y = 0) {
      if (point_x <> 0 ){
        Primops.reverted <- true;
      }
      (* ... *)
    } else {
      ret_y <- (-point_y) %% Constants.Q;
    }
    return (ret_x, ret_y);
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
    
lemma pointNegate_low_equiv_mid (memory: mem) (point_address: uint256) (point_x_int point_y_int: int): equiv [
    PointNegate.low ~ PointNegate.mid :
      arg{2} = (point_x_int, point_y_int) /\
      arg{1} = point_address /\
      point_y_int < Constants.Q /\
      Primops.memory{1} = memory /\
      W256.to_uint(PurePrimops.mload memory point_address) = point_x_int /\
      W256.to_uint(PurePrimops.mload memory (point_address + W256.of_int 32)) = point_y_int /\
      !Primops.reverted{1} /\
      !Primops.reverted{2}
      ==>
      (Primops.reverted{1} <=> Primops.reverted{2}) /\ (
        (!Primops.reverted{1} /\ (
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory point_address (W256.of_int res{2}.`1)) (point_address + W256.of_int 32) (W256.of_int res{2}.`2)))
        \/
        (Primops.reverted{1} /\ point_y_int = 0 /\ point_x_int <> 0)
     )
].
proof. proc.
seq 2 2 : (#pre /\ _2{1} = (usr_point{1} + W256.of_int 32) /\ ret_x{2} = point_x{2} /\ ret_y{2} = point_y{2} /\ W256.to_uint usr_pY{1} = point_y{2}).
call {1} (ConcretePrimops.mload_pspec memory (point_address + W256.of_int 32)). wp. skip. progress.

if. smt (@W256).
seq 1 0 : (#pre /\ W256.to_uint tmp90{1} = point_x{2} /\ point_y{2} = 0).
call {1} (ConcretePrimops.mload_pspec memory point_address). skip. progress; try smt (@W256).

case (point_x_int <> 0).
rcondt {1} 1.
progress. skip. progress. smt ().
rcondt {2} 1.
progress.
call{1} revertWithMessage_low_pspec.
wp. skip. progress. by smt ().
rcondf {1} 1.
progress. skip. progress. rewrite -W256.to_uintK H3 H5. smt ().
rcondf {2} 1.
progress. skip. progress. smt (). smt (). left. progress. 
do 2! (rewrite store_loaded_val). reflexivity.

    simplify.
exists* _2{1},  usr_pY{1}. elim*. move => _2_l usr_pY_l.
call {1} (ConcretePrimops.mstore_pspec memory _2_l ((of_int Constants.Q)%W256 - usr_pY_l)).
wp. skip. progress. smt (). smt (). left. progress.
rewrite store_loaded_val. congr.
rewrite -W256.to_uintK -H2. rewrite aux. smt (@W256). smt (@W256). smt (@W256).
qed.
