pragma Goals:printall.

require import Logic UInt256 Memory Array.

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

(* Lemmas for proving load store properties *)

lemma add_neq:
    forall (x: uint256) (y: int),
    1 <= y /\ y < 32 => x <> x + W256.of_int y.
    proof.
      progress.
      smt.
    qed.

lemma shl_zero (x: uint256):
    x `<<<` 0 = x.
proof.
    apply W256.ext_eq.
    progress.
    smt.
qed.

lemma shr_zero (x: uint256):
    x `>>>` 0 = x.
proof.
    apply W256.ext_eq.
    progress.
    smt.
qed.

(* done between 1 and 32 for now because that's all we need and it's easier on smt *)
lemma get_set_offset (m: mem) (idx: uint256) (offset: int) (val: uint256):
    0 < offset /\ offset < 32 => m.[idx+W256.of_int offset<-val].[idx] = m.[idx].
proof.
    progress.
    apply Map.get_set_neqE.
    apply add_neq.
    smt.
qed.

lemma get_set_offsets_neq (m: mem) (idx: uint256) (offset1 offset2: int) (val: uint256):
    0 <= offset1 /\ 0 <= offset2 /\ offset1 < 32 /\ offset2 < 32 /\ offset1 <> offset2 =>
    m.[idx+W256.of_int offset1<-val].[idx+W256.of_int offset2] = m.[idx+W256.of_int offset2].
proof.
    progress.
    apply Map.get_set_neqE.
    smt.
qed.

lemma masklsb_zero:
    W256.masklsb 0 = W256.zero.
proof.
    smt.
qed.

lemma splitMask_zero (x: uint256):
    (splitMask W256.zero x).`2 = x.
proof.
    rewrite /splitMask.
    simplify.
    smt.
qed.

lemma splitMask2_shr_shl (i: int) (x: uint256):
    (0 <= i /\ i < 256) => 
    (splitMask (W256.masklsb i) x).`2 `>>>` i `<<<` i =
    (splitMask (W256.masklsb i) x).`2.
proof.
    progress.
    apply W256.ext_eq.
    progress.
    rewrite /splitMask.
    simplify.
    smt.
qed.

lemma splitMask_add_comm mask (w: uint256):
    (splitMask mask w).`2 + (splitMask mask w).`1 = w.
proof.
    rewrite addrC.
    apply splitMask_add.
qed.

