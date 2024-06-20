pragma Goals:printall.

require import Logic UInt256 Memory YulPrimops Array Real.
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

module PointNegate = {
  proc low(point: uint256) : unit = {
    var x, y;
    x <@ Primops.mload(point);
    y <@ Primops.mload(point + W256.of_int 32);
    if (x = W256.zero /\ y = W256.zero) {
      Primops.revert();
    } else {
      if (y <> W256.zero) {
        Primops.mstore(point + W256.of_int 32, p - y);
      }
    }
  }
}.

lemma pointNegate_actual_matches_low: equiv [
    Test.pointNegate ~ PointNegate.low :
    Primops.memory{1} = Primops.memory{2} /\
      arg{1} = arg{2} /\
    !Primops.reverted{1} /\
    !Primops.reverted{2}
      ==>
        Primops.reverted{1} <=> Primops.reverted{2} /\
        !Primops.reverted{1} =>
        forall (idx: uint256),
        Primops.memory{1}.[idx] =
        Primops.memory{2}.[idx]
    ].
    proof.
      exists* Primops.memory{1}.
      elim*=>memory.
      exists* point{1}.
      elim*=>point.
      proc.
      case (ConcretePrimops.mload memory (point+W256.of_int 32) = W256.zero).
      rcondt{1} 6.
      progress.
      wp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      wp.
      skip.
      progress.
      case (ConcretePrimops.mload memory point = W256.zero).
      rcondt{1} 8.
      progress.
      wp.
      call (ConcretePrimops.mload_spec memory point).
      wp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      wp.
      skip.
      progress.
      inline Primops.revert.
      rcondt{2} 3.
      progress.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point).
      skip.
      progress.
      wp.
      progress.
      inline Primops.mload.
      wp.
      skip.
      progress.
      rcondf{1} 8.
      progress.
      wp.
      call (ConcretePrimops.mload_spec memory point).
      wp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      wp.
      skip.
      progress.
      rcondf{2} 3.
      progress.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point).
      skip.
      progress.
      rewrite H1 H2.
      trivial.
      wp.
      rcondf{2} 3.
      progress.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point).
      skip.
      progress.
      inline Primops.mload.
      wp.
      skip.
      progress.
      rcondf{1} 6.
      progress.
      wp.
      sp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      skip.
      progress.
      rcondf{2} 3.
      progress.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point).
      skip.
      progress.
      rewrite H1.
      trivial.
      rcondt{2} 3.
      progress.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point).
      skip.
      progress.
      sp.
      sim.
      inline Primops.mstore. (*TODO why doesn't call work here*)
      sim.
      inline Primops.mload.
      wp.
      skip.
      progress.
qed.
      
lemma pointNegate_low_correctness :
    forall (x y point_addr : uint256),
hoare [ PointNegate.low :
    arg = point_addr /\
    (x <> W256.zero \/ y <> W256.zero) /\
        Primops.memory.[point_addr] = x /\
        Primops.memory.[point_addr + (W256.of_int 32)] = y /\
      y < p /\
      Primops.reverted = false ==>
    (
        Primops.reverted = false =>
    (
        Primops.memory.[point_addr] = x /\
        Primops.memory.[point_addr + (W256.of_int 32)] = (-y) %% p
    )
  )].
proof.
  admit.
qed.

      
lemma pointNegate_correctness :
    forall (x y point_addr : uint256),
hoare [ Test.pointNegate :
    arg = point_addr /\
    (x <> W256.zero \/ y <> W256.zero) /\
        Primops.memory.[point_addr] = x /\
        Primops.memory.[point_addr + (W256.of_int 32)] = y /\
      y < p /\
      Primops.reverted = false ==>
    (
        Primops.reverted = false =>
    (
        Primops.memory.[point_addr] = x /\
        Primops.memory.[point_addr + (W256.of_int 32)] = (-y) %% p
    )
  )]. proof.
      progress.
      bypr.
      move => &m h.
      have low: Pr[PointNegate.low(arg{m}) @ &m :
     ! (Primops.reverted = false =>
        Primops.memory.[point_addr] = x /\
      Primops.memory.[point_addr + (of_int 32)%W256] = (-y) %% p)] = 0%r.
      admit.
      rewrite - low.
      byequiv pointNegate_actual_matches_low.
      progress.
      smt.
      smt.
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
