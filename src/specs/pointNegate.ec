pragma Goals:printall.

require import AllCore Int IntDiv Constants Field.
require import Memory PurePrimops UInt256 Utils YulPrimops.

import FieldQ.

type Point = F * F.

print asint.

pred IsPointValid (point: Point) =
  !(point.`1 <> FieldQ.zero /\ point.`2 = FieldQ.zero).

(* High *)
op pointNegate (point: Point): Point option =
  if !IsPointValid point then None else Some (point.`1, -(point.`2)).

module PointNegate = {

  proc usr_revertWithMessage(usr_len : uint256, usr_reason : uint256): unit = {
  var _1, _2, _3, _4, _5, _6, _7;
  _1 <- (PurePrimops.shl (W256.of_int 229) (W256.of_int 4594637));
  _2 <- (W256.of_int 0);
  Primops.mstore(_2, _1);
  _3 <- (W256.of_int 32);
  _4 <- (W256.of_int 4);
  Primops.mstore(_4, _3);
  _5 <- (W256.of_int 36);
  Primops.mstore(_5, usr_len);
  _6 <- (W256.of_int 68);
  Primops.mstore(_6, usr_reason);
  _7 <- (W256.of_int 100);
  Primops.revert(_2, _7);
  }

  proc usr_pointNegate(usr_point : uint256): unit = {
    var _1, _2, usr_pY, tmp88, tmp89, _3, tmp90, _4, _5, tmp91, _6, _7;
    _1 <- (W256.of_int 32);
    _2 <- (usr_point + _1);
    tmp88 <@ Primops.mload(_2);
    usr_pY <- tmp88;
    tmp89 <- usr_pY;
    if ((tmp89 = (W256.of_int 0)))
      {
      tmp90 <@ Primops.mload(usr_point);
      _3 <- tmp90;
      if (bool_of_uint256 _3)
        {
        _4 <- PurePrimops.STRING (*pointNegate: invalid point*);
        _5 <- (W256.of_int 26);
        tmp91 <@ usr_revertWithMessage(_5, _4);
        }
      }
    else {
      _6 <- (W256.of_int Q);
      _7 <- (_6 - usr_pY);
      Primops.mstore(_2, _7);
      }
    }

  proc low(usr_point : uint256): unit = {
    var _2, usr_pY, tmp90, tmp91, _6, _7 : uint256;
    _2 <- (usr_point + W256.of_int 32);
    usr_pY <@ Primops.mload(_2);
    if ((usr_pY = (W256.of_int 0))) {
      tmp90 <@ Primops.mload(usr_point);
      if (bool_of_uint256 tmp90) {
        usr_revertWithMessage((W256.of_int 26), PurePrimops.STRING);
        }
    }
    else {
      Primops.mstore(_2, ((W256.of_int Q) - usr_pY));
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
    } else {
      ret_y <- (-point_y) %% Q;
    }
    return (ret_x, ret_y);
  }
}.

lemma usr_revertWithMessage_correctness (size reason : uint256) :
  phoare [ PointNegate.usr_revertWithMessage : arg = (size, reason) ==> Primops.reverted ] = 1%r.
proof.
progress.
proc.
inline Primops.mload Primops.mstore Primops.revert.
wp.
skip.
progress.
qed.

print usr_revertWithMessage_correctness.

lemma pointNegate_extracted_equiv_low :
   equiv [PointNegate.usr_pointNegate ~ PointNegate.low : ={arg, glob PointNegate} ==> ={res}].
proof. proc.
seq 5  2 : (#pre /\ ={usr_pY, _2} /\ usr_pY{1} = tmp89{1}).
wp.
call (_: ={glob PointNegate}). wp. skip. auto.
wp. auto.
if. auto. 
inline *. sp. wp.
skip. auto.
call (_: ={glob PointNegate}). auto. wp. auto.
qed.

lemma pointNegate_low_equiv_mid (memory: mem) (point_address: uint256) (point_x_int point_y_int: int): equiv [
    PointNegate.low ~ PointNegate.mid :
      arg{2} = (point_x_int, point_y_int) /\ arg{1} = point_address /\ Primops.memory{1} = memory /\
      W256.to_uint(PurePrimops.mload memory point_address) = point_x_int /\
      W256.to_uint(PurePrimops.mload memory (point_address + W256.of_int 32)) = point_y_int /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      Primops.reverted{1} <=> Primops.reverted{2} /\ (
        (!Primops.reverted{1} /\ (
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory point_address (W256.of_int res{2}.`1)) (point_address + W256.of_int 32) (W256.of_int res{2}.`2)))
        \/
        (Primops.reverted{1} /\ point_y_int = 0 /\ point_x_int <> 0)
     )
].
proof. proc.
seq 2 2 : (#pre /\ ret_x{2} = point_x{2} /\ ret_y{2} = point_y{2} /\ W256.to_uint usr_pY{1} = point_y{2}).
call {1} (ConcretePrimops.mload_pspec memory (point_address + W256.of_int 32)). wp. skip. progress.

if. smt (@W256).
seq 1 0 : (#pre /\ W256.to_uint tmp90{1} = point_x{2} /\ point_y{2} = 0).
call {1} (ConcretePrimops.mload_pspec memory point_address). skip. progress; try smt (@W256).

if. smt (@W256).
call {1} (usr_revertWithMessage_correctness (of_int 26)%W256 PurePrimops.STRING).
wp. skip. progress. right. smt(@W256). skip. progress.

simplify.
exists* _2{1},  usr_pY{1}. elim*. move => _2_l usr_pY_l.
call {1} (ConcretePrimops.mstore_pspec memory _2_l ((of_int Q)%W256 - usr_pY_l)).
wp. skip. progress.
qed.
