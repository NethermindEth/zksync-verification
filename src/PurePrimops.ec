pragma Goals:printall.

require import Array.
require import Logic.
require import Memory.
require export UInt256.
require import Utils.

theory PurePrimops.

(* definitions ========== *)

op calldata : uint256 array.
op keccak256_f : uint256 array -> uint256.

op iszero(v : uint256) : uint256 = if (v = W256.zero) then W256.one else  W256.zero.
op eq_uint256(a : uint256, b : uint256) : uint256  = if a = b then W256.one else W256.zero.
op gt_uint256 (x y : uint256)  = if y < x then W256.one else W256.zero.
op slt_uint256 (x y : uint256) = if uint256_as_signed x < uint256_as_signed y then W256.one else W256.zero.

op mload (memory: mem) (idx: uint256) =
    memory.[idx+ W256.of_int 31] +
    (memory.[idx+ W256.of_int 30] `<<<` 8) +
    (memory.[idx+ W256.of_int 29] `<<<` 16) +
    (memory.[idx+ W256.of_int 28] `<<<` 24) +
    (memory.[idx+ W256.of_int 27] `<<<` 32) +
    (memory.[idx+ W256.of_int 26] `<<<` 40) +
    (memory.[idx+ W256.of_int 25] `<<<` 48) +
    (memory.[idx+ W256.of_int 24] `<<<` 56) +
    (memory.[idx+ W256.of_int 23] `<<<` 64) +
    (memory.[idx+ W256.of_int 22] `<<<` 72) +
    (memory.[idx+ W256.of_int 21] `<<<` 80) +
    (memory.[idx+ W256.of_int 20] `<<<` 88) +
    (memory.[idx+ W256.of_int 19] `<<<` 96) +
    (memory.[idx+ W256.of_int 18] `<<<` 104) +
    (memory.[idx+ W256.of_int 17] `<<<` 112) +
    (memory.[idx+ W256.of_int 16] `<<<` 120) +
    (memory.[idx+ W256.of_int 15] `<<<` 128) +
    (memory.[idx+ W256.of_int 14] `<<<` 136) +
    (memory.[idx+ W256.of_int 13] `<<<` 144) +
    (memory.[idx+ W256.of_int 12] `<<<` 152) +
    (memory.[idx+ W256.of_int 11] `<<<` 160) +
    (memory.[idx+ W256.of_int 10] `<<<` 168) +
    (memory.[idx+ W256.of_int 9] `<<<` 176) +
    (memory.[idx+ W256.of_int 8] `<<<` 184) +
    (memory.[idx+ W256.of_int 7] `<<<` 192) +
    (memory.[idx+ W256.of_int 6] `<<<` 200) +
    (memory.[idx+ W256.of_int 5] `<<<` 208) +
    (memory.[idx+ W256.of_int 4] `<<<` 216) +
    (memory.[idx+ W256.of_int 3] `<<<` 224) +
    (memory.[idx+ W256.of_int 2] `<<<` 232) +
    (memory.[idx+ W256.of_int 1] `<<<` 240) +
    (memory.[idx] `<<<` 248)
    axiomatized by mLoadE.

op mstore (memory: mem) (idx val: uint256): mem.

op mulmod(a b n : uint256) : uint256 =
  let a_int = W256.to_uint a in
  let b_int = W256.to_uint b in
  let n_int = W256.to_uint n in
  W256.of_int ((a_int * b_int) %% n_int)
axiomatized by mulmodE.

op addmod(a b n : uint256) : uint256 =
  let a_int = W256.to_uint a in
  let b_int = W256.to_uint b in
  let n_int = W256.to_uint n in
  W256.of_int ((a_int + b_int) %% n_int)
axiomatized by addmodE.

op bit_and(a : uint256, b : uint256) : uint256 = a `&` b
axiomatized by bit_andE.

op shl(a : uint256, b : uint256) : uint256 = a `<<<` (W256.to_uint b)
axiomatized by shlE.

op shr(a : uint256, b : uint256) : uint256 = a `>>>` (W256.to_uint b)
axiomatized by shrE.

op STRING : uint256 = W256.zero.


(* lemmas =========== *)

(* iszero *)
lemma iszero_zeroE : iszero (W256.zero) = W256.one.
    proof.
      rewrite /iszero.
      simplify.
      trivial.
  qed.
lemma iszero_nonzeroE (val: uint256) : val <> W256.zero => iszero val = W256.zero.
    proof.
      progress.
      rewrite /iszero.
      smt ().
  qed.

(* mstore *)
op words_overlap (address1 address2: uint256) =
  (exists (offset: int), 0 <= offset /\ offset < 32 /\ address1 + W256.of_int offset = address2) \/
  (exists (offset: int), 0 <= offset /\ offset < 32 /\ address2 + W256.of_int offset = address1)
  axiomatized by words_overlapE.

lemma subK (a b c: uint256): a - b <> a - c => b <> c.
    proof.
      progress.
      (* smt (@W256). *)
      smt iterate.
  qed.

lemma sub_self (a: uint256): a - a = W256.zero.
    proof.
      smt (@W256).
  qed.

lemma sub_add (a b c: uint256): a - (b + c) = a - b - c.
    proof.
      admit.
      (* smt timeout=1000. *)
  qed.

lemma mod_of_lt (a b: int): 0 < a => 0 < b => a < b => a %% b = a.
    proof.
      smt ().
  qed.

lemma get_right (a b c: int): a <= b < c => b < c.
    proof.
      smt().
    qed.

lemma add_neq_of_lt (idx idx2: uint256) (offset: int):
    W256.of_int 31 < idx2 - idx =>  0 <= offset /\ offset < 32 => (idx + W256.of_int offset) <> idx2.
    proof.
      progress.
      rewrite W256.ultE W256.of_uintK in H.
      apply (subK idx2).
      rewrite sub_self.
      rewrite sub_add.
      rewrite /W256.ulift2.
      have Lifted: W256.of_int (W256.to_uint (idx2 - idx) - offset) <> W256.of_int 0.
      pose diff := to_uint (idx2 - idx).
      have diff_gt:  31 < diff.
      rewrite /diff.
      rewrite (mod_of_lt 31 W256.modulus) in H; trivial.
      have diff_lt: diff < W256.modulus.
      rewrite /diff.
      exact (get_right 0 (to_uint (idx2 - idx)) W256.modulus (W256.to_uint_cmp (idx2 - idx))).
      smt (@W256).
      smt (@W256).
  qed.

lemma no_overlap (idx idx2: uint256):
    W256.of_int 31 < idx - idx2 => W256.of_int 31 < idx2 - idx => !words_overlap idx idx2.
    proof.
      progress.
      smt (add_neq_of_lt).
  qed.

op uint256_frame (memory_pre memory_post: mem) (idx: uint256) = forall (idx2: uint256), W256.of_int 31 < idx2 - idx => memory_post.[idx2] = memory_pre.[idx2].

axiom mload_mstore_same (memory: mem) (idx val: uint256):
  mload (mstore memory idx val) idx = val.

axiom mstore_frame (memory: mem) (idx val: uint256):
  uint256_frame memory (mstore memory idx val) idx.

axiom mstore_of_load_and_frame (memory_pre memory_post: mem) (idx val: uint256):
  mload memory_post idx = val =>
  uint256_frame memory_pre memory_post idx =>
  memory_post = mstore memory_pre idx val.

lemma apply_mstore_mload_diff (memory: mem) (idx idx2 val: uint256):
    W256.of_int 31 < idx2 - idx => W256.of_int 31 < idx - idx2 =>  mload (mstore memory idx val) idx2 = mload memory idx2.
proof.
  progress.
  rewrite /mload.
  pose memory_post := mstore memory idx val.
  have h_full: mload memory_post idx = val /\ uint256_frame memory memory_post idx. by smt.
  have h_frame: uint256_frame memory memory_post idx. smt.
  rewrite /uint256_frame in h_frame.
  have h31: forall (offset: int), 0 <= offset => offset < 32 => memory_post.[idx2 + W256.of_int offset] = memory.[idx2 + W256.of_int offset].
  progress.
  apply h_frame.
  rewrite /W256.\ult.
  rewrite W256.of_uintK.
  rewrite mod_of_lt; trivial.
  by smt timeout=100.
  have h0: memory_post.[idx2] = memory.[idx2] by smt.
  (rewrite (h31 31); first trivial); first trivial.
  (rewrite (h31 30); first trivial); first trivial.
  (rewrite (h31 29); first trivial); first trivial.
  (rewrite (h31 28); first trivial); first trivial.
  (rewrite (h31 27); first trivial); first trivial.
  (rewrite (h31 26); first trivial); first trivial.
  (rewrite (h31 25); first trivial); first trivial.
  (rewrite (h31 24); first trivial); first trivial.
  (rewrite (h31 23); first trivial); first trivial.
  (rewrite (h31 22); first trivial); first trivial.
  (rewrite (h31 21); first trivial); first trivial.
  (rewrite (h31 20); first trivial); first trivial.
  (rewrite (h31 19); first trivial); first trivial.
  (rewrite (h31 18); first trivial); first trivial.
  (rewrite (h31 17); first trivial); first trivial.
  (rewrite (h31 16); first trivial); first trivial.
  (rewrite (h31 15); first trivial); first trivial.
  (rewrite (h31 14); first trivial); first trivial.
  (rewrite (h31 13); first trivial); first trivial.
  (rewrite (h31 12); first trivial); first trivial.
  (rewrite (h31 11); first trivial); first trivial.
  (rewrite (h31 10); first trivial); first trivial.
  (rewrite (h31 9); first trivial); first trivial.
  (rewrite (h31 8); first trivial); first trivial.
  (rewrite (h31 7); first trivial); first trivial.
  (rewrite (h31 6); first trivial); first trivial.
  (rewrite (h31 5); first trivial); first trivial.
  (rewrite (h31 4); first trivial); first trivial.
  (rewrite (h31 3); first trivial); first trivial.
  (rewrite (h31 2); first trivial); first trivial.
  (rewrite (h31 1); first trivial); first trivial.
    rewrite h0.
    reflexivity.
qed.

end PurePrimops.
