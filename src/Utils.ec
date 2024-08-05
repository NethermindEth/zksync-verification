pragma Goals:printall.

require import AllCore.
require import Array.
require import EllipticCurve.
require import Logic.
require import UInt256.
import StdOrder.

  (* option *)

lemma exists_of_is_some ['a] (ov : 'a option) : is_some ov => exists (v : 'a), ov = Some v. progress. smt (). qed.

lemma odflt_some_eq ['a] (a b : 'a) : odflt a (Some b) = b. smt (). qed.
  
lemma is_none_iff_not_is_some (a: 'a option): is_none a <=> !is_some a.
    proof.
      case (a = None). smt (). smt ().
  qed.
  
lemma neg_none_eq_some ['a] (o : 'a option) : (!(is_none o)) = is_some o. smt (). qed.

lemma is_none_of_eq_none ['a] (o : 'a option) : o = None => is_none o. smt (). qed.

lemma eq_none_of_is_none ['a] (o : 'a option) : is_none o => o = None. smt (). qed.

(* Some potentially useful lemmas to prove mid-level specs *)

lemma lt_trans : forall (a b c : int), a < b => b < c => a < c. progress. smt (). qed.
lemma le_trans : forall (a b c : int), a <= b => b <= c => a <= c. progress. smt (). qed.

lemma mod_m_lt_m :
    forall (a m : int), 0 < m => a %% m < m.
    smt ().
    qed.

lemma mod_eq_self : forall (a m : int), 0 < m => 0 <= a => a < m => a %% m = a.
    smt ().
  qed.

lemma mod_plus : forall (a m : int), a %% m = (a + m) %% m. progress. smt (@IntDiv). qed.

lemma mod_mod_eq_mod :
    forall (m1 m2 v : int), 0 < m1 => m1 <= m2 => (v %% m1) %% m2 = v %% m1.
    progress.
    smt ().
  qed.

lemma sub_mono_lt (a b c : int) : 0 <= b => a < c => a - b < c. progress. smt(). qed.
  
 (* tuples *)
lemma proj1 ['a 'b] (x1 : 'a) (x2 : 'b) : (x1, x2).`1 = x1. smt (). qed.
lemma proj2 ['a 'b] (x1 : 'a) (x2 : 'b) : (x1, x2).`2 = x2. smt (). qed.
  
(* uint256 lemmas *)

lemma add_zero (x: uint256): x + W256.zero = x by smt(@W256).

lemma uint256_distrib_sub (a b c : uint256) : a - (b + c) = (a - c) - b. smt (@W256). qed.
    
lemma neq_small (x y: int):
    0 <= x < W256.modulus =>
    0 <= y < W256.modulus =>
    x <> y =>
    W256.of_int x <> W256.of_int y.
    proof.
      progress.
      case (W256.of_int x < W256.of_int y).
      progress. smt (@W256).
      progress.
      case (W256.of_int y < W256.of_int x).
      progress. smt (@W256).
      progress.
      case (W256.of_int x = W256.of_int y).
      progress.
      have h_lte_1: (W256.of_int y <= W256.of_int x) by smt (@W256).
      have h_lte_2: (W256.of_int x <= W256.of_int y) by smt (@W256).
      have h_eq: (W256.of_int x = W256.of_int y) by smt(@W256).
      have h_neq: (W256.to_uint(W256.of_int(x)) <> W256.to_uint(W256.of_int(y))).
      rewrite W256.of_uintK W256.of_uintK.
      rewrite pmod_small. smt ().
      rewrite pmod_small. smt ().
      exact H3.
      smt().
      by progress.
    qed.

lemma uint256_eq_of_eq (a b : uint256) : W256.to_uint a = W256.to_uint b => a = b.
    smt.
  qed.

lemma uint256_eq_of_eq' (a b : int) : a = b => W256.of_int a = W256.of_int b. progress. qed.
    
lemma uint256_neq_of_neq (a b : uint256) : W256.to_uint a <> W256.to_uint b => a <> b.
    smt.
  qed.
  
lemma uint256_lt_of_lt (a b : uint256) : W256.to_uint a < W256.to_uint b => a < b.
    smt.
  qed.

lemma uint256_lt_of_lt' (a b : uint256) : a < b => W256.to_uint a < W256.to_uint b.
    smt.
  qed.

lemma uint256_le_of_le (a b : uint256) : W256.to_uint a <= W256.to_uint b => a <= b.
    smt.
  qed.

lemma uint256_le_of_le' (a b : uint256) : a <= b => W256.to_uint a <= W256.to_uint b.
    smt.
  qed.
    
lemma uint256_cast_add (a b : uint256) : (a + b) = W256.of_int ((W256.to_uint a + W256.to_uint b) %% W256.modulus).
    rewrite addE /ulift2. smt.
  qed.

lemma uint256_cast_neg (a : uint256) : - a = W256.of_int ((- (W256.to_uint a)) %% W256.modulus).
    rewrite oppE /ulift1. smt.
  qed.
  
lemma uint256_cast_sub (a b : uint256) : (a - b) = W256.of_int ((W256.to_uint a - W256.to_uint b) %% W256.modulus).
    rewrite oppE /ulift1 uint256_cast_add.
    apply uint256_eq_of_eq.
    rewrite of_uintK of_uintK of_uintK.
    pose ai := to_uint a.
    pose bi := to_uint b.
    smt (@IntDiv).
  qed.

lemma uint256_cast_mul (a b : uint256) : (a * b) = W256.of_int ((W256.to_uint a * W256.to_uint b) %% W256.modulus).
    rewrite mulE /ulift2. smt.
  qed.

lemma mod_mod_eq_mod' (a m : int) : (a %% m) %% m = a %% m.
    smt (@IntDiv).
  qed.

lemma mod_lt_of_ge (a b m : int) : a < m => b < m => m < a + b => (a + b)%%m < b.
    progress.
    smt.
  qed.

lemma overflow_lem (a b m : int) : a < m => b < m => m <= a + b => (a + b) %% m = a + b - m.
    progress.
    smt.
  qed.


lemma neg_eq (a : uint256) : - a = W256.of_int (W256.modulus - W256.to_uint a).
    smt timeout=10.
  qed.

lemma uint256_eq (a : uint256) : a = - (- a).
    smt (@W256).
  qed.

lemma uint256_zero_sub_eq_sub (a : uint256) : W256.zero - a = - a.
    smt (@W256).
  qed.

lemma uint256_sub_zero_eq (a : uint256) : a - W256.zero = a.
    smt (@W256).
  qed.

lemma uint256_sub_distr2 (a b c : uint256) : a - (b + c) = (a - c) - b.
    smt (@W256).
  qed.

lemma uint256_le_le_trans (a b c : uint256) : a <= b => b <= c => a <= c. smt (@W256). qed.
lemma uint256_le_lt_trans (a b c : uint256) : a <= b => b < c => a <= c. smt (@W256). qed.
lemma uint256_lt_lt_trans (a b c : uint256) : a < b => b < c => a < c. smt (@W256). qed.
  
lemma uint256_ord1 (a b c : uint256) : W256.to_uint a + W256.to_uint c <= W256.to_uint b => c <= b => a <= b - c.
    progress.
    smt.
  qed.
    

lemma uint256_size (a : uint256) : W256.to_uint a < W256.modulus.
    have H := W256.to_uint_cmp a. smt. qed.
  
lemma uint256_ord2 (a b : uint256) : a < b => a < a - b.
    progress.
    rewrite uint256_cast_sub.
    apply uint256_lt_of_lt.
    rewrite of_uintK mod_mod_eq_mod'.
    have H' : to_uint a < to_uint b. smt.
    have HA : W256.to_uint a < W256.modulus. exact uint256_size.
    have HB : W256.to_uint a < W256.modulus. exact uint256_size.
    have H0 : - W256.modulus < to_uint a - to_uint b. smt.
    have H'' : (to_uint a - to_uint b) %% W256.modulus = W256.modulus + to_uint a - to_uint b.
    smt.
    rewrite H''. smt.
  qed.

lemma uint256_ord2' (a b : uint256) : a < b => a <= a - b.
    progress.
    have H1 := uint256_ord2 _ _ H.
    smt (@W256).
  qed.
    
lemma uint256_ord3 (a b : uint256) : W256.zero < a => a < b => - b < - a.
    progress.
    rewrite neg_eq neg_eq.
    have H' := uint256_lt_of_lt' a b H0.
    apply uint256_lt_of_lt.
    rewrite of_uintK of_uintK.
    have HA : W256.to_uint a < W256.modulus. exact uint256_size.
    have HB : W256.to_uint b < W256.modulus. exact uint256_size.
    have HA' : W256.modulus - to_uint a < W256.modulus. smt (@W256).
    have HB' : W256.modulus - to_uint b < W256.modulus. smt (@W256).
    have HA'' : (W256.modulus - to_uint a) %% W256.modulus = W256.modulus - to_uint a. smt.
    have HB'' : (W256.modulus - to_uint b) %% W256.modulus = W256.modulus - to_uint b. smt.
    rewrite HA'' HB''.
    smt ().
  qed.

lemma uint256_ord3' (a b : uint256) : W256.zero < a => a < - b => b < - a.
    progress.
    rewrite (uint256_eq b).
    apply uint256_ord3.
    exact H.
    exact H0.
  qed.

lemma uint256_mod_eq_of_lt (a m : uint256) : a < m => a %% m = a.
    proof.
      progress. rewrite umodE /ulift2.
      have H' : W256.to_uint a < W256.to_uint m. apply uint256_lt_of_lt'. exact H.
      apply uint256_eq_of_eq.
      rewrite of_uintK.
      rewrite mod_mod_eq_mod. smt (@W256). have T := uint256_size m.
      have T' : forall (a b : int), a < b => a <= b. smt ().
      apply T'. exact T.
      pose av := to_uint a.
      pose mv := to_uint m.
      have H12 : 0 <= to_uint a. smt (@W256).
      smt (@IntDiv).
  qed.

lemma cast_uint256_mod_eq_of_lt (a p : int) : 0 <= a < p < W256.modulus => W256.of_int a = (W256.of_int a) %% (W256.of_int p).
    proof.
      progress.
      rewrite uint256_mod_eq_of_lt.
      apply uint256_lt_of_lt.
      rewrite to_uint_small.
      smt ().
      rewrite to_uint_small.
      smt ().
      exact H0.
      reflexivity.
  qed.
  
lemma add_neq:
    forall (x: uint256) (y: int),
    1 <= y /\ y < W256.modulus => x <> x + W256.of_int y.
    proof.
      progress.
      rewrite uint256_cast_add.
      rewrite of_uintK uint256_neq_of_neq.
      rewrite W256.to_uint_small.
      smt (@IntDiv).
      pose xi := to_uint x.
      smt (@IntDiv).
      trivial.
    qed.

lemma add_2_neq (x y: int) (a: uint256):
    0 <= x =>
    0 <= y =>
    x < W256.modulus =>
    y < W256.modulus =>
    x <> y =>
    a + W256.of_int x <> a + W256.of_int y.
    proof.
      progress.
      rewrite uint256_cast_add.
      rewrite of_uintK.
      rewrite uint256_cast_add.
      rewrite of_uintK.
      rewrite uint256_neq_of_neq.
      rewrite W256.to_uint_small.
      smt (@IntDiv).
      pose ai := to_uint a.
      rewrite W256.to_uint_small.
      smt (@IntDiv).
      smt (@IntDiv).
      trivial.
  qed.

lemma add_2_neq' (x y: int) (a: uint256):
    (x %% W256.modulus) <> (y %% W256.modulus) =>
    a + W256.of_int x <> a + W256.of_int y.
    proof.
      progress.
      rewrite uint256_cast_add.
      rewrite of_uintK.
      rewrite uint256_cast_add.
      rewrite of_uintK.
      rewrite uint256_neq_of_neq.
      rewrite W256.to_uint_small.
      smt (@IntDiv).
      pose ai := to_uint a.
      rewrite W256.to_uint_small.
      smt (@IntDiv).
      smt (@IntDiv).
      trivial.
  qed.

lemma neq_of_lt (idx idx2: uint256):
    W256.of_int 31 < idx2 - idx => idx2 <> idx.
proof.
  progress.
  have H' : (of_int 31)%W256 < (of_int ((to_uint idx2 - to_uint idx) %% W256.modulus))%W256.
  have H''' := uint256_cast_sub idx2 idx.
  rewrite -H'''. exact H.
  have H'' := uint256_lt_of_lt' _ _ H'.
  rewrite of_uintK of_uintK mod_mod_eq_mod' in H''.
  apply uint256_neq_of_neq.
  pose idxv := to_uint idx.
  pose idx2v := to_uint idx2.
  smt (@IntDiv).
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
      rewrite uint256_cast_add uint256_cast_add of_uintK of_uintK.
      apply uint256_neq_of_neq.
      rewrite of_uintK of_uintK mod_mod_eq_mod' mod_mod_eq_mod'.
      rewrite uint256_cast_sub in H.
      rewrite uint256_cast_sub in H0.
      have L1 : 32 %% W256.modulus = 32. smt ().
      have H' := uint256_le_of_le' _ _ H.
      have H0' := uint256_le_of_le' _ _ H0.
      rewrite of_uintK of_uintK mod_mod_eq_mod' in H'.
      rewrite of_uintK of_uintK mod_mod_eq_mod' in H0'.
      rewrite L1 in H'.
      rewrite L1 in H0'.
  
      pose idx2v := to_uint idx2.
      pose idxv := to_uint idx.
      smt timeout=100.
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

lemma small_neg_mono (a b c : uint256) : a <= b => c <= a => a - c <= b - c.
    progress.
    rewrite uint256_cast_sub uint256_cast_sub.
    apply uint256_le_of_le.
    rewrite to_uint_small. smt ().
    rewrite to_uint_small. smt ().
    have H'  := uint256_le_of_le' _ _ H.
    have H0' := uint256_le_of_le' _ _ H0.
    pose av := W256.to_uint a.
    pose bv := W256.to_uint b.
    pose cv := W256.to_uint c.
    have H1' : cv <= bv. smt ().
    have HA : av < W256.modulus. exact (uint256_size _).
    have HB : bv < W256.modulus. exact (uint256_size _).
    have HC : cv < W256.modulus. exact (uint256_size _).
    have HA' : 0 <= av. smt (@W256).
    have HB' : 0 <= bv. smt (@W256).
    have HC' : 0 <= cv. smt (@W256).
    rewrite mod_eq_self. smt (). smt ().
    apply (StdOrder.IntOrder.ler_lt_trans av).
    smt (). exact HA.
    rewrite mod_eq_self. smt (). smt ().
    have INT : bv - cv <= bv. smt ().
    apply (StdOrder.IntOrder.ler_lt_trans bv).
    smt (). exact HB.
    smt ().
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

(* smt cannot prove these in the proof because there's too many assumptions in play *)
lemma diff_96 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= a - W256.of_int 96.
    proof.
      progress.
      rewrite uint256_cast_sub of_uintK.
      have ->: 96 %% W256.modulus = 96. smt ().
      have H'  : W256.to_uint a < W256.modulus. exact uint256_size.
      have H'' : 128 <= W256.to_uint a.
      have T' : 128 %% W256.modulus = 128. smt ().
      have T := uint256_le_of_le' _ _ H.
      rewrite of_uintK in T.
      rewrite T' in T.
      exact T.
      have J : to_uint a - 96 < to_uint a. smt (). 
      have ->: (to_uint a - 96) %% W256.modulus = to_uint a - 96.
      rewrite mod_eq_self. smt (). smt ().
      exact (lt_trans  _ _ _ J H').
      reflexivity.
      apply uint256_le_of_le.
      rewrite of_uintK of_uintK.
      have ->: 32 %% W256.modulus = 32. smt ().
      rewrite mod_eq_self. smt (). smt ().
      exact (lt_trans _ _ _ J H').
      smt ().
  qed.
  
lemma diff_64 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= a - W256.of_int 64.
    proof.
      progress.
      rewrite uint256_cast_sub of_uintK.
      have ->: 64 %% W256.modulus = 64. smt ().
      have H'  : W256.to_uint a < W256.modulus. exact uint256_size.
      have H'' : 128 <= W256.to_uint a.
      have T' : 128 %% W256.modulus = 128. smt ().
      have T := uint256_le_of_le' _ _ H.
      rewrite of_uintK in T.
      rewrite T' in T.
      exact T.
      have J : to_uint a - 64 < to_uint a. smt (). 
      have ->: (to_uint a - 64) %% W256.modulus = to_uint a - 64.
      rewrite mod_eq_self. smt (). smt ().
      exact (lt_trans  _ _ _ J H').
      reflexivity.
      apply uint256_le_of_le.
      rewrite of_uintK of_uintK.
      have ->: 32 %% W256.modulus = 32. smt ().
      rewrite mod_eq_self. smt (). smt ().
      exact (lt_trans _ _ _ J H').
      smt ().
  qed.
  
lemma diff_32 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= a - W256.of_int 32.
    proof.
      progress.
      rewrite uint256_cast_sub of_uintK.
      have ->: 32 %% W256.modulus = 32. smt ().
      have H'  : W256.to_uint a < W256.modulus. exact uint256_size.
      have H'' : 128 <= W256.to_uint a.
      have T' : 128 %% W256.modulus = 128. smt ().
      have T := uint256_le_of_le' _ _ H.
      rewrite of_uintK in T.
      rewrite T' in T.
      exact T.
      have J : to_uint a - 32 < to_uint a. smt (). 
      have ->: (to_uint a - 32) %% W256.modulus = to_uint a - 32.
      rewrite mod_eq_self. smt (). smt ().
      exact (lt_trans  _ _ _ J H').
      reflexivity.
      apply uint256_le_of_le.
      rewrite of_uintK of_uintK.
      have ->: 32 %% W256.modulus = 32. smt ().
      rewrite mod_eq_self. smt (). smt ().
      exact (lt_trans _ _ _ J H').
      smt ().
  qed.

lemma diff_0 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= a - W256.zero.
    proof.
      progress.
      have J : 128 %% W256.modulus = 128. smt ().
      have H' := uint256_le_of_le' _ _ H.
      rewrite of_uintK J in H'.
      apply uint256_le_of_le.
      rewrite uint256_sub_zero_eq of_uintK.
      smt ().
  qed.

lemma lt_sub_sub (a b c : int) : c < b => a - b < a - c. smt (). qed.
lemma le_sub_sub (a b c : int) : c <= b => a - b <= a - c. smt (). qed.
lemma lt_sub_sub' (a b c : int) : b < c => b - a < c - a. smt (). qed.
lemma le_sub_sub' (a b c : int) : b <= c => b - a <= c - a. smt (). qed.
lemma le_of_lt (a b : int) : a < b => a <= b. smt (). qed.
lemma lt_sub (a b : int) : b < a => -a < - b. smt (). qed.

lemma mod_eq_sub_self : forall (a m : int), 0 < m => a < 0 => - m < a => a %% m = m + a.
    progress.
    smt (@IntDiv).
  qed.
  
lemma diff_neg_96 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= -a => W256.of_int 32 <= W256.of_int 96 - a.
    proof.
      progress.
      have E : 128 %% W256.modulus = 128. smt ().
      have E' : 32 %% W256.modulus = 32. smt ().
      have H' := uint256_le_of_le' _ _ H.
      have H0' := uint256_le_of_le' _ _ H0.
      rewrite of_uintK E in H'.
      rewrite of_uintK E' in H0'.
      rewrite uint256_cast_sub.
      rewrite of_uintK.
      have ->: 96 %% W256.modulus = 96. smt ().
      apply uint256_le_of_le.
      rewrite of_uintK of_uintK mod_mod_eq_mod'.
      have ->: 32 %% W256.modulus = 32. smt ().
      have J := uint256_size a.
      have ->: (96 - to_uint a) %% W256.modulus = W256.modulus - (W256.to_uint a - 96).
      have J1 : - W256.modulus < 96 - to_uint a.
      apply (lt_trans _ (- W256.to_uint a) _).
      apply lt_sub.
      exact J.
      smt ().
      rewrite mod_eq_sub_self. smt (). smt ().
      exact J1.
      smt ().
      have J' : W256.to_uint a - 96 < W256.modulus - 96.
      apply lt_sub_sub'.
      exact J.
      have J'' : W256.modulus - (W256.modulus - 96) < W256.modulus - (to_uint a - 96). apply lt_sub_sub. exact J'.
      apply (le_trans _ (W256.modulus - (W256.modulus - 96)) _).
      have ->: W256.modulus - (W256.modulus - 96) = 96. smt ().
      smt ().
      apply le_sub_sub.
      apply le_sub_sub'.
      apply le_of_lt.
      exact J.
  qed.  
  
lemma diff_neg_64 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= -a => W256.of_int 32 <= W256.of_int 64 - a.
    proof.
      progress.
      have E : 128 %% W256.modulus = 128. smt ().
      have E' : 32 %% W256.modulus = 32. smt ().
      have H' := uint256_le_of_le' _ _ H.
      have H0' := uint256_le_of_le' _ _ H0.
      rewrite of_uintK E in H'.
      rewrite of_uintK E' in H0'.
      rewrite uint256_cast_sub.
      rewrite of_uintK.
      have ->: 64 %% W256.modulus = 64. smt ().
      apply uint256_le_of_le.
      rewrite of_uintK of_uintK mod_mod_eq_mod'.
      have ->: 32 %% W256.modulus = 32. smt ().
      have J := uint256_size a.
      have ->: (64 - to_uint a) %% W256.modulus = W256.modulus - (W256.to_uint a - 64).
      have J1 : - W256.modulus < 64 - to_uint a.
      apply (lt_trans _ (- W256.to_uint a) _).
      apply lt_sub.
      exact J.
      smt ().
      rewrite mod_eq_sub_self. smt (). smt ().
      exact J1.
      smt ().
      have J' : W256.to_uint a - 64 < W256.modulus - 64.
      apply lt_sub_sub'.
      exact J.
      have J'' : W256.modulus - (W256.modulus - 64) < W256.modulus - (to_uint a - 64). apply lt_sub_sub. exact J'.
      apply (le_trans _ (W256.modulus - (W256.modulus - 64)) _).
      have ->: W256.modulus - (W256.modulus - 64) = 64. smt ().
      smt ().
      apply le_sub_sub.
      apply le_sub_sub'.
      apply le_of_lt.
      exact J.
  qed.
  
lemma diff_neg_32 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= -a => W256.of_int 32 <= W256.of_int 32 - a.
    proof.
          progress.
      have E : 128 %% W256.modulus = 128. smt ().
      have E' : 32 %% W256.modulus = 32. smt ().
      have H' := uint256_le_of_le' _ _ H.
      have H0' := uint256_le_of_le' _ _ H0.
      rewrite of_uintK E in H'.
      rewrite of_uintK E' in H0'.
      rewrite uint256_cast_sub.
      rewrite of_uintK.
      have ->: 32 %% W256.modulus = 32. smt ().
      apply uint256_le_of_le.
      rewrite of_uintK of_uintK mod_mod_eq_mod'.
      have ->: 32 %% W256.modulus = 32. smt ().
      have J := uint256_size a.
      have ->: (32 - to_uint a) %% W256.modulus = W256.modulus - (W256.to_uint a - 32).
      have J1 : - W256.modulus < 32 - to_uint a.
      apply (lt_trans _ (- W256.to_uint a) _).
      apply lt_sub.
      exact J.
      smt ().
      rewrite mod_eq_sub_self. smt (). smt ().
      exact J1.
      smt ().
      have J' : W256.to_uint a - 32 < W256.modulus - 32.
      apply lt_sub_sub'.
      exact J.
      have J'' : W256.modulus - (W256.modulus - 32) < W256.modulus - (to_uint a - 32). apply lt_sub_sub. exact J'.
      apply (le_trans _ (W256.modulus - (W256.modulus - 32)) _).
      have ->: W256.modulus - (W256.modulus - 32) = 32. smt ().
      smt ().
      apply le_sub_sub.
      apply le_sub_sub'.
      apply le_of_lt.
      exact J.
  qed.
  
lemma diff_neg_0 (a: uint256): W256.of_int 128 <= a => W256.of_int 32 <= -a => W256.of_int 32 <= W256.zero - a.
    proof.
      progress.
  qed.

(* logic *)
  
lemma weaken_and_left (a b): a /\ b => a. proof. by smt(). qed.
lemma weaken_and_right (a b): a /\ b => b. proof. by smt(). qed.
  
require import Constants.
  
lemma mod_R_W256_mod_R (n : int) : n %% Constants.R %% W256.modulus = n %% R. proof. by smt(). qed.
lemma R_mod_W256_R : R %% W256.modulus = R. by smt(). qed.      

 (* Finite field lemmas *)
lemma F_eq_inzmod_asint (x : F) : ZModField.inzmod (ZModField.asint x) = x. smt (@ZModField). qed.
