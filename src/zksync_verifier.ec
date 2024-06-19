pragma Goals:printall.

require import Logic UInt256 Memory YulPrimops Array.
require import Utils.

op p = W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583.

module Test = {
    proc pointNegate(point : uint256) : unit = {
      var _1, _2, _3, pY, tmp166, tmp167, tmp168, _6, _7;
      _1 <- W256.of_int 32;
      _2 <- point + _1;
      tmp166 <@ Primops.mload(_2);
      pY <- tmp166;
      tmp167 <- pY;
      if (tmp167 = W256.of_int 0)
      {
        tmp168 <@ Primops.mload(point);
        _3 <- tmp168;
        if (_3 = W256.of_int 0)
        {
          Primops.revert();
        }
      } else {
          _6 <- W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583;
          _7 <- _6 - pY;
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
      
lemma pointNegate_correctness :
    forall (x y point_addr : uint256),
hoare [ Test.pointNegate :
    arg = point_addr /\
    (x <> W256.zero \/ y <> W256.zero) /\
        Primops.memory.[point_addr] = x /\
        Primops.memory.[point_addr + (W256.of_int 32)] = y /\
        y < p ==>
    (
        Primops.reverted = false =>
    (
        Primops.memory.[point_addr] = x /\
        Primops.memory.[point_addr + (W256.of_int 32)] = (-y) %% p
    )
)]. proof.
    progress.
    proc.
    simplify.
    inline Primops.mload Primops.mstore Primops.revert.
    wp.
    skip.
    progress.
    rewrite H1.
    admit.
    rewrite Map.get_set_neqE.
    admit.
    auto.
    rewrite Map.get_set_sameE.
    admit.
qed.
