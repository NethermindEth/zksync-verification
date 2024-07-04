require import UInt256.
require export CoreMap SmtMap.

type uint8 = W8.t.
type mem = (uint256, uint8) map.
(* pred mem_wellformed (memory: mem) = forall (idx: uint256), memory.[idx] <= W256.masklsb 8. *)

(* lemma write_byte_maintains_wellformed (memory: mem) (idx val: uint256):
    val < W256.masklsb 8 =>
    mem_wellformed memory =>
    mem_wellformed (memory.[idx <- val]).
    proof.
      progress.
      smt ().
  qed. *)

print W32u8.

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
  .[idx + (W256.of_int 31) <- bytes.[31]].

op load (memory: mem) (idx: uint256): uint256 =
  W32u8.pack32_t (W32u8.Pack.init (fun (i: int) => memory.[idx + W256.of_int i])).

  (* pack32wE *)
search W32u8.\bits8.
search W256."_.[_]".

(* from utils *)
lemma add_neq:
    forall (x: uint256) (y: int),
    1 <= y /\ y < 32 => x <> x + W256.of_int y.
    proof.
      progress.
      smt.
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

lemma add_zero (x: uint256): x + W256.zero = x by smt(@W256).

lemma load_store (memory: mem) (idx val: uint256):
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

    
