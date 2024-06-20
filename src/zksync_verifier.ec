pragma Goals:printall.

require import Logic UInt256 Memory YulPrimops Array.
require import Utils.

op p = W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583.

module Test = {

    proc usr_revertWithMessage(usr_len : uint256, usr_reason : uint256): unit = {
    var _1, _2, _3, _4, _5, _6, _7;
    _1 <- (shl (W256.of_int 229) (W256.of_int 4594637));
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
        _4 <- STRING (*pointNegate: invalid point*);
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
  }.

    (* Functional correctness *)

lemma writeReadTest_correctness :
    forall (address value: uint256),
hoare [ Test.writeReadTest :
      arg = (address, value) ==>
      res = value].
proof.
    progress.
  proc.
  exists* Primops.memory.
  elim*=>memory_pre.
  call (ConcretePrimops.mload_spec (ConcretePrimops.apply_mstore memory_pre address value) address).
  call (ConcretePrimops.mstore_spec memory_pre address value).
  skip.
  progress.
  apply ConcretePrimops.apply_mstore_mload_same.
qed.

lemma usr_revertWithMessage_correctness :
    forall (size reason : uint256),
hoare [ Test.usr_revertWithMessage :
      arg = (size, reason) ==>
    Primops.reverted = true
    ].
    proof.
      progress.
      proc.
      inline Primops.mload Primops.mstore Primops.revert.
      wp.
      skip.
      progress.
  qed.

lemma pointNegate_correctness :
    forall (x y point_addr : uint256),
hoare [ Test.usr_pointNegate :
      arg = point_addr /\
      (x <> W256.zero \/ y <> W256.zero) /\
        ConcretePrimops.mload Primops.memory point_addr = x /\
        ConcretePrimops.mload Primops.memory (point_addr + (W256.of_int 32)) = y /\
        y < p ==>
      (
        Primops.reverted = false =>
        (
          ConcretePrimops.mload Primops.memory point_addr = x /\
          ConcretePrimops.mload Primops.memory (point_addr + (W256.of_int 32)) = (-y) %% p
        )
      )
    ]. proof.
        progress.
        proc.
        exists* Primops.memory.
        elim*=>memory_pre.
        sp.
        seq 1 : (_1 = (of_int 32)%W256 /\
      _2 = point_addr + (of_int 32)%W256 /\
      memory_pre = Primops.memory /\
      usr_point = point_addr /\
      tmp88 = y /\
      (x <> W256.zero \/ y <> W256.zero) /\
      (ConcretePrimops.mload Primops.memory point_addr)%ConcretePrimops = x /\
      (ConcretePrimops.mload Primops.memory (point_addr + (of_int 32)%W256))%ConcretePrimops = y /\
        y < p).
        call (ConcretePrimops.mload_spec memory_pre (point_addr + (of_int 32)%W256)).
        skip.
        progress.
        sp.
        if.
        seq 1 :
    (memory_pre = Primops.memory /\
      usr_point = point_addr /\
      tmp88 = y /\
      tmp89 = y /\
      tmp90 = x /\
      usr_pY = y /\
      (x <> W256.zero \/ y <> W256.zero) /\
      (ConcretePrimops.mload Primops.memory point_addr)%ConcretePrimops = x /\
      (ConcretePrimops.mload Primops.memory (point_addr + (of_int 32)%W256))%ConcretePrimops = y /\
        y < p /\
      y = W256.zero).
        call (ConcretePrimops.mload_spec memory_pre point_addr).
        skip.
        progress.
        sp.
        if.
        sp.
        (* should do this better *)
        inline Test.usr_revertWithMessage Primops.revert.
        wp.
        progress.
        skip.
        progress.
        rewrite H1.
        rewrite neg_w256_zero_eq_w256_zero umodE /ulift2.
        progress.
        sp.
        call (ConcretePrimops.mstore_spec memory_pre (point_addr + (of_int 32)%W256) ((of_int
        21888242871839275222246405745257275088696311157297823662689037894645226208583)%W256 - y)).
        skip.
        progress.
        rewrite ConcretePrimops.mload_apply_mstore_eq_mload_of_disj.
        smt.
        reflexivity.
        rewrite ConcretePrimops.apply_mstore_mload_same -/p umodE /ulift2.
        admit.
  qed.
