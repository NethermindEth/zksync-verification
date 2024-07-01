pragma Goals:printall.

require import AllCore Int IntDiv Constants Field.
(* require import Memory PurePrimops UInt256 Utils YulPrimops. *)

type Point = FieldQ.F * FieldQ.F.

pred IsPointValid (point: Point) =
  !(point.`1 <> zero /\ point.`2 = zero).

(* High *)
op pointNegate (point: Point): Point option =
  if !IsPointValid point then None else Some (point.`1, -(point.`2)).

module PointNegate = {
  proc usr_pointNegate'(usr_point : uint256): unit = {
    var _2, usr_pY,  tmp90, tmp91, _6, _7 : uint256;
    _2 <- (usr_point + W256.of_int 32);
    usr_pY <@ Primops.mload(_2);
    if ((usr_pY = (W256.of_int 0)))
      {
      tmp90 <@ Primops.mload(usr_point);
      if (bool_of_uint256 tmp90)
        {
        usr_revertWithMessage((W256.of_int 26), PurePrimops.STRING);
        }
      }
    else {
      Primops.mstore(_2, ((W256.of_int (asint Q)) - usr_pY));
      }
    }

  (* proc low(point: uint256) : unit = { *)
  (*   var x, y; *)
  (*   x <@ Primops.mload(point); *)
  (*   y <@ Primops.mload(point + W256.of_int 32); *)
  (*   if (y <> W256.zero) { *)
  (*       Primops.mstore(point + W256.of_int 32, p_uint256 - y); *)
  (*   } *)
    
  (*   if (x <> W256.zero /\ y = W256.zero) { *)
  (*     Primops.revert(W256.zero, W256.zero); *)
  (*   } *)
  (* } *)

  proc mid(point_x: int, point_y: int) : int * int = {
    var ret_x, ret_y;
    ret_x <- point_x;
    ret_y <- point_y;
    if (point_y = 0) {
      if (point_x <> 0 ){
        Primops.reverted <- true;
      }
    } else {
        ret_y <- (-point_y) %% p_int;
    }
    return (ret_x, ret_y);
  }
  
  (* proc mid(point_x: int, point_y: int) : int * int = { *)
  (*   var ret_x, ret_y; *)
  (*   ret_x <- point_x; *)
  (*   ret_y <- (-point_y) %% p_int; *)

  (*   if (point_x <> 0 /\ point_y = 0) { *)
  (*     Primops.reverted <- true; *)
  (*   } *)

  (*   return (ret_x, ret_y); *)
  (* } *)

  (*     proc high(point: Point): Point = { *)
  (*   (* option instead of revert *) *)
  (*   if (!IsPointValid point) { *)
  (*     Primops.reverted <- true; *)
  (*   } *)

  (*   return (NegatePoint point); *)
  (* } *)
}.

(* DENIS *)

module Test = {
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
      _6 <- (W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583);
      _7 <- (_6 - usr_pY);
      Primops.mstore(_2, _7);
      }
    }
    proc writeReadTest(address: uint256, value: uint256): uint256 = {
      var _1;
      Primops.mstore(address, value);
      _1 <@ Primops.mload(address);
      return _1;
    }
    
  proc usr_pointNegate'(usr_point : uint256): unit = {
    var _2, usr_pY,  tmp90, tmp91, _6, _7 : uint256;
    _2 <- (usr_point + W256.of_int 32);
    usr_pY <@ Primops.mload(_2);
    if ((usr_pY = (W256.of_int 0)))
      {
      tmp90 <@ Primops.mload(usr_point);
      if (bool_of_uint256 tmp90)
        {
        usr_revertWithMessage((W256.of_int 26), PurePrimops.STRING);
        }
      }
    else {
      Primops.mstore(_2, ((W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583) - usr_pY));
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
        ret_y <- (-point_y) %% p_int;
    }
    return (ret_x, ret_y);
  }
  }.


lemma boring_proof1 : equiv [Test.usr_pointNegate ~ Test.usr_pointNegate' : ={arg, glob Test} ==> ={glob Test} /\ ={res}].
proc. 
seq 5  2 : (#pre /\ ={usr_pY, _2} /\ usr_pY{1} = tmp89{1}).
wp.
call (_: ={glob Test}). wp. skip. auto.
wp. auto.
if. auto. 
inline *. sp. wp.
skip. auto.
call (_: ={glob Test}). auto. wp. auto.
qed.

lemma boring_proof2 (memory: mem) (point_address: uint256) (point_x_int point_y_int: int): equiv [
    Test.usr_pointNegate' ~ Test.mid :
      ={glob Test} /\ (* revise *)
      arg{2} = (point_x_int, point_y_int) /\ arg{1} = point_address /\
      Primops.memory{1} = memory /\
      W256.to_uint(PurePrimops.mload memory point_address) = point_x_int /\
      W256.to_uint(PurePrimops.mload memory (point_address + W256.of_int 32)) = point_y_int /\
      !Primops.reverted{1} /\ !Primops.reverted{2}
      ==>
      Primops.reverted{1} <=> Primops.reverted{2} /\ (
        (!Primops.reverted{1}) /\ (
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory point_address (W256.of_int res{2}.`1)) (point_address + W256.of_int 32) (W256.of_int res{2}.`2)
        )
            \/
        (Primops.reverted{1}) /\ ( (* .. *) )
      )
    ].
proof. proc.
