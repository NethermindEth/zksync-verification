pragma Goals:printall.

require import Logic UInt256 Memory YulPrimops Array.

op p = W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583.

module Test = {

  proc pointNegate(m : mem, point : uint256) : mem = {
      var _1, _2, _3, pY, tmp166, tmp167, tmp168, _6, _7, tmp170;
      Primops.m <- m;
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
        }
        (* tmp170 <- Primops.m; *)
      } else {
          _6 <- W256.of_int 21888242871839275222246405745257275088696311157297823662689037894645226208583;
          _7 <- _6 - pY;
          tmp170 <@ Primops.mstore(_2, _7);
      }
      return Primops.m;
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
    forall (m : mem) (point_addr : uint256),
    (m.[point_addr] <> W256.zero \/ m.[point_addr + (W256.of_int 32)] <> W256.zero) /\ m.[point_addr + (W256.of_int 32)] < p  =>
        hoare [ Test.pointNegate : arg = (m, point_addr) ==>
          (m.[point_addr] = res.[point_addr] /\ res.[point_addr + (W256.of_int 32)] = (- m.[point_addr + (W256.of_int 32)]) %% p)].
            progress.
            proc.
            simplify.
            inline Primops.mload Primops.mstore.
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
