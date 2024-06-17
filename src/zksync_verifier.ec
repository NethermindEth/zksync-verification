pragma Goals:printall.

require import Logic UInt256 Memory YulPrimops Array.

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

}.

(* Some potentially useful lemmas to prove mid-level specs *)

lemma mod_m_lt_m :
    forall (a m : int), 0 < m => a %% m < m.
    smt ().
    qed.

lemma mod_eq_self : forall (a m : int), 0 < m => 0 <= a => a < m => a %% m = a.
    smt ().
    qed.

lemma mod_mod_eq_mod :
    forall (m1 m2 v : int), 0 < m1 => m1 <= m2 => (v %% m1) %% m2 = v %% m1.
    progress.
    smt ().
    qed.

(* Functional correctness *)


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
