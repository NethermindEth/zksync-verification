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
  (* TODO use apply_mstore_def *)
  apply ConcretePrimops.apply_mstore_def.
    call (ConcretePrimops.mload_spec Primops.memory{2} address).
    inline Primops.mstore Primops.mload.
    wp.
    skip.
    move => &hr hr_eq.
    move => x248 x240 x232 x224 x216 x208 x200 x192 x184 x176 x168 x160 x152 x144 x136 x128 x120 x112 x104 x96 x88 x80 x72 x64 x56 x48 x40 x32 x24 x16 x8.
    move => memory.
    rewrite {1} /memory.
    rewrite Map.get_set_sameE.
    rewrite {1} /memory.
    rewrite get_set_offsets_neq; first trivial.
    rewrite Map.get_set_sameE.
    rewrite masklsb_zero.
    rewrite shr_zero.
    rewrite splitMask_zero.
    rewrite /x8.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 2! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 3! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 4! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 5! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 6! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 7! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 8! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 9! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 10! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 11! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 12! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 13! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 14! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 15! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 16! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x128.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 17! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x136.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 18! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x144.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 19! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x152.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 20! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x160.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 21! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x168.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 22! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x176.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 23! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x184.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 24! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x192.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 25! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x200.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 26! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x208.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 27! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x216.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 28! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x224.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 29! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x232.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 30! (rewrite get_set_offsets_neq; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x240.
    rewrite splitMask2_shr_shl. trivial.
    rewrite splitMask_add.
    rewrite {1} /memory.
    do 31! (rewrite get_set_offset; first trivial).
    rewrite Map.get_set_sameE.
    rewrite /x248.
    rewrite splitMask2_shr_shl; first trivial.
    rewrite splitMask_add.
    have injection: forall (a b c d: uint256), (a, b) = (c, d) => b = d.
    progress.
    smt.
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
