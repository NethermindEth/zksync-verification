pragma Goals:printall.

require import AllCore.
require import IntDiv.
require import UInt256.
require import Utils.
require export CoreMap SmtMap.

theory MemoryMap.

type mem = (uint256, uint8) map.

op store (memory: mem) (idx val: uint256) =
    let bytes = W32u8.unpack8 val in
  memory
  .[idx <- bytes.[0]]
  .[idx + (W256.of_int 1) <- bytes.[1]]
  .[idx + (W256.of_int 2) <- bytes.[2]]
  .[idx + (W256.of_int 3) <- bytes.[3]]
  .[idx + (W256.of_int 4) <- bytes.[4]]
  .[idx + (W256.of_int 5) <- bytes.[5]]
  .[idx + (W256.of_int 6) <- bytes.[6]]
  .[idx + (W256.of_int 7) <- bytes.[7]]
  .[idx + (W256.of_int 8) <- bytes.[8]]
  .[idx + (W256.of_int 9) <- bytes.[9]]
  .[idx + (W256.of_int 10) <- bytes.[10]]
  .[idx + (W256.of_int 11) <- bytes.[11]]
  .[idx + (W256.of_int 12) <- bytes.[12]]
  .[idx + (W256.of_int 13) <- bytes.[13]]
  .[idx + (W256.of_int 14) <- bytes.[14]]
  .[idx + (W256.of_int 15) <- bytes.[15]]
  .[idx + (W256.of_int 16) <- bytes.[16]]
  .[idx + (W256.of_int 17) <- bytes.[17]]
  .[idx + (W256.of_int 18) <- bytes.[18]]
  .[idx + (W256.of_int 19) <- bytes.[19]]
  .[idx + (W256.of_int 20) <- bytes.[20]]
  .[idx + (W256.of_int 21) <- bytes.[21]]
  .[idx + (W256.of_int 22) <- bytes.[22]]
  .[idx + (W256.of_int 23) <- bytes.[23]]
  .[idx + (W256.of_int 24) <- bytes.[24]]
  .[idx + (W256.of_int 25) <- bytes.[25]]
  .[idx + (W256.of_int 26) <- bytes.[26]]
  .[idx + (W256.of_int 27) <- bytes.[27]]
  .[idx + (W256.of_int 28) <- bytes.[28]]
  .[idx + (W256.of_int 29) <- bytes.[29]]
  .[idx + (W256.of_int 30) <- bytes.[30]]
  .[idx + (W256.of_int 31) <- bytes.[31]]
axiomatized by storeE.

op load (memory: mem) (idx: uint256): uint256 =
  W32u8.pack32_t (W32u8.Pack.init (fun (i: int) => memory.[idx + W256.of_int i]))
axiomatized by loadE.

lemma load_store_same (memory: mem) (idx val: uint256):
    load (store memory idx val) idx = val.
    proof.
      rewrite /load /store.
      simplify.
      apply W256.ext_eq.
      progress.
      rewrite W32u8.pack32wE. smt().
      rewrite W32u8.get_bits8. smt().
      pose byte_idx := x %/ 8.
      rewrite W32u8.Pack.initE.
      progress.
      have H_byte_idx : 0 <= byte_idx && byte_idx < 32. smt().
      rewrite H_byte_idx. simplify.
      congr.
      smt (add_2_neq @W32u8 add_zero).
  qed.

op uint256_frame (memory_pre memory_post: mem) (idx: uint256) =
  forall (idx2: uint256), W256.of_int 32 <= idx2 - idx => memory_pre.[idx2] = memory_post.[idx2]
axiomatized by uint256_frameE.

lemma store_frame (memory: mem) (idx val: uint256):
    uint256_frame memory (store memory idx val) idx.
    proof.
      rewrite uint256_frameE.
      progress.
      rewrite storeE.
      simplify.
      do 31! (rewrite Map.get_set_neqE; first exact add_neq_of_diff).
      rewrite Map.get_set_neqE; first exact (neq_of_diff idx idx2).
      reflexivity.
    qed.

lemma store_loaded_val (memory: mem) (idx: uint256):
    store memory idx (load memory idx) = memory.
    proof.
      rewrite /store /load.
      smt(@W32u8).
  qed.



lemma load_store_diff (memory: mem) (idx idx2 val: uint256):
    W256.of_int 32 <= idx2 - idx => W256.of_int 32 <= idx - idx2 => load (store memory idx val) idx2 = load memory idx2.
    proof.
      progress.
      rewrite loadE loadE.
      apply W256.ext_eq. progress.
      rewrite W32u8.pack32wE. trivial.
      rewrite W32u8.pack32wE. trivial.
      congr.
      pose y := x %/ 8.
      have H_y_lower: 0 <= y by smt (@IntDiv).
      have H_y_upper: y < 32 by smt (@IntDiv).
      rewrite W32u8.Pack.initE.
      rewrite W32u8.Pack.initE. simplify. congr.
      rewrite storeE. simplify.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff).
      rewrite Map.get_set_neqE. smt(@Utils).
      reflexivity.
    qed.
      
      

    (* done between 1 and 32 for now because that's all we need and it's easier on smt *)
lemma get_set_offset (m: mem) (idx: uint256) (offset: int) (val: uint8):
    0 < offset /\ offset < 32 => m.[idx+W256.of_int offset<-val].[idx] = m.[idx].
proof.
    progress.
    apply Map.get_set_neqE.
    apply add_neq.
    smt ().
qed.

lemma get_set_offsets_neq (m: mem) (idx: uint256) (offset1 offset2: int) (val: uint8):
    0 <= offset1 /\ 0 <= offset2 /\ offset1 < 32 /\ offset2 < 32 /\ offset1 <> offset2 =>
    m.[idx+W256.of_int offset1<-val].[idx+W256.of_int offset2] = m.[idx+W256.of_int offset2].
proof.
    progress.
    apply Map.get_set_neqE.
    have H3': offset2 <> offset1 by smt ().
    exact add_2_neq.
qed.
  
end MemoryMap.
