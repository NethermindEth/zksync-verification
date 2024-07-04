pragma Goals:printall.

require import Array.
require import Logic.
require import UInt256.

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

  
(* uint256 lemmas *)

lemma add_zero (x: uint256): x + W256.zero = x by smt(@W256).

lemma add_neq:
    forall (x: uint256) (y: int),
    1 <= y /\ y < 32 => x <> x + W256.of_int y.
    proof.
      progress.
      smt timeout=100.
    qed.

lemma add_2_neq (x y: int) (a: uint256):
    0 <= x =>
    0 <= y =>
    x < 32 =>
    y < 32 =>
    x <> y =>
    a + W256.of_int x <> a + W256.of_int y.
    proof.
      progress.
      smt.
  qed.

lemma neq_of_lt (idx idx2: uint256):
    W256.of_int 31 < idx2 - idx => idx2 <> idx.
proof.
    progress.
    smt timeout=100.
qed.

lemma neg_add_eq (a: uint256): (-a) + a = W256.zero.
    proof.
      smt(@W256).
  qed.

lemma add_neq_of_diff (idx idx2: uint256) (i: int):
    W256.of_int 32 <= idx2 - idx =>
    0 <= i =>
    i < 32 =>
    idx2 <> idx + W256.of_int i.
    proof.
      progress.
    case (idx2 <> idx + W256.of_int i). smt ().
      (*proof by contradiction *)
    change (idx2 = idx + W256.of_int i => false).
    move=> H_eq.
      have H': W256.of_int 32 <= idx2 - idx by exact H.
      rewrite H_eq addrC in H'.
      rewrite addrA in H'.
      rewrite neg_add_eq in H'.
      rewrite W256.add0r_s in H'.
      rewrite W256.ule_of_int in H'.
      rewrite pmod_small in H'. smt().
      rewrite pmod_small in H'. smt().
      smt().
  qed.

lemma add_2_neq_of_diff (idx idx2: uint256) (a b: int):
    W256.of_int 32 <= idx2 - idx =>
    W256.of_int 32 <= idx - idx2 =>
    0 <= a =>
    a < 32 =>
    0 <= b =>
    b < 32 =>
    idx2 + (W256.of_int a) <> idx + W256.of_int b.
    proof.
      progress.
      smt.
    qed.

lemma neq_of_diff (idx idx2: uint256):
    W256.of_int 32 <= idx2 - idx =>
    idx2 <> idx.
    proof.
      progress.
      have H_add_zero: idx2 <> idx + W256.zero by exact add_neq_of_diff.
      rewrite addr0_s in H_add_zero.
      assumption.
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
    smt timeout=100.
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

lemma mul_add_mod_eq (a b m : int) : 0 < m => ((m * a) + b) %% m = b %% m.
    smt ().
  qed.

lemma weaken_and_left (a b): a /\ b => a by smt().
lemma weaken_and_right (a b): a /\ b => b by smt().