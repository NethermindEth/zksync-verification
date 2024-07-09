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
  .[idx <- bytes.[31]]
  .[idx + (W256.of_int 1) <- bytes.[30]]
  .[idx + (W256.of_int 2) <- bytes.[29]]
  .[idx + (W256.of_int 3) <- bytes.[28]]
  .[idx + (W256.of_int 4) <- bytes.[27]]
  .[idx + (W256.of_int 5) <- bytes.[26]]
  .[idx + (W256.of_int 6) <- bytes.[25]]
  .[idx + (W256.of_int 7) <- bytes.[24]]
  .[idx + (W256.of_int 8) <- bytes.[23]]
  .[idx + (W256.of_int 9) <- bytes.[22]]
  .[idx + (W256.of_int 10) <- bytes.[21]]
  .[idx + (W256.of_int 11) <- bytes.[20]]
  .[idx + (W256.of_int 12) <- bytes.[19]]
  .[idx + (W256.of_int 13) <- bytes.[18]]
  .[idx + (W256.of_int 14) <- bytes.[17]]
  .[idx + (W256.of_int 15) <- bytes.[16]]
  .[idx + (W256.of_int 16) <- bytes.[15]]
  .[idx + (W256.of_int 17) <- bytes.[14]]
  .[idx + (W256.of_int 18) <- bytes.[13]]
  .[idx + (W256.of_int 19) <- bytes.[12]]
  .[idx + (W256.of_int 20) <- bytes.[11]]
  .[idx + (W256.of_int 21) <- bytes.[10]]
  .[idx + (W256.of_int 22) <- bytes.[9]]
  .[idx + (W256.of_int 23) <- bytes.[8]]
  .[idx + (W256.of_int 24) <- bytes.[7]]
  .[idx + (W256.of_int 25) <- bytes.[6]]
  .[idx + (W256.of_int 26) <- bytes.[5]]
  .[idx + (W256.of_int 27) <- bytes.[4]]
  .[idx + (W256.of_int 28) <- bytes.[3]]
  .[idx + (W256.of_int 29) <- bytes.[2]]
  .[idx + (W256.of_int 30) <- bytes.[1]]
  .[idx + (W256.of_int 31) <- bytes.[0]]
axiomatized by storeE.

op load (memory: mem) (idx: uint256): uint256 =
  W32u8.pack32_t (W32u8.Pack.init (fun (i: int) => memory.[idx + W256.of_int (31 - i)]))
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
      case (byte_idx = 0). move => HB0. rewrite HB0. smt (@SmtMap).
      move => HB0. case (byte_idx = 1). move => HB1. rewrite HB1. simplify. smt (@SmtMap add_2_neq).
      move => HB1. case (byte_idx = 2). move => HB2. rewrite HB2. simplify. smt (@SmtMap add_2_neq).
      move => HB2. case (byte_idx = 3). move => HB3. rewrite HB3. simplify. smt (@SmtMap add_2_neq).
      move => HB3. case (byte_idx = 4). move => HB4. rewrite HB4. simplify. smt (@SmtMap add_2_neq).
      move => HB4. case (byte_idx = 5). move => HB5. rewrite HB5. simplify. smt (@SmtMap add_2_neq).
      move => HB5. case (byte_idx = 6). move => HB6. rewrite HB6. simplify. smt (@SmtMap add_2_neq).
      move => HB6. case (byte_idx = 7). move => HB7. rewrite HB7. simplify. smt (@SmtMap add_2_neq).
      move => HB7. case (byte_idx = 8). move => HB8. rewrite HB8. simplify. smt (@SmtMap add_2_neq).
      move => HB8. case (byte_idx = 9). move => HB9. rewrite HB9. simplify. smt (@SmtMap add_2_neq).
      move => HB9. case (byte_idx = 10). move => HB10. rewrite HB10. simplify. smt (@SmtMap add_2_neq).
      move => HB10. case (byte_idx = 11). move => HB11. rewrite HB11. simplify. smt (@SmtMap add_2_neq).
      move => HB11. case (byte_idx = 12). move => HB12. rewrite HB12. simplify. smt (@SmtMap add_2_neq).
      move => HB12. case (byte_idx = 13). move => HB13. rewrite HB13. simplify. smt (@SmtMap add_2_neq).
      move => HB13. case (byte_idx = 14). move => HB14. rewrite HB14. simplify. smt (@SmtMap add_2_neq).
      move => HB14. case (byte_idx = 15). move => HB15. rewrite HB15. simplify. smt (@SmtMap add_2_neq).
      move => HB15. case (byte_idx = 16). move => HB16. rewrite HB16. simplify. smt (@SmtMap add_2_neq).
      move => HB16. case (byte_idx = 17). move => HB17. rewrite HB17. simplify. smt (@SmtMap add_2_neq).
      move => HB17. case (byte_idx = 18). move => HB18. rewrite HB18. simplify. smt (@SmtMap add_2_neq).
      move => HB18. case (byte_idx = 19). move => HB19. rewrite HB19. simplify. smt (@SmtMap add_2_neq).
      move => HB19. case (byte_idx = 20). move => HB20. rewrite HB20. simplify. smt (@SmtMap add_2_neq).
      move => HB20. case (byte_idx = 21). move => HB21. rewrite HB21. simplify. smt (@SmtMap add_2_neq).
      move => HB21. case (byte_idx = 22). move => HB22. rewrite HB22. simplify. smt (@SmtMap add_2_neq).
      move => HB22. case (byte_idx = 23). move => HB23. rewrite HB23. simplify. smt (@SmtMap add_2_neq).
      move => HB23. case (byte_idx = 24). move => HB24. rewrite HB24. simplify. smt (@SmtMap add_2_neq).
      move => HB24. case (byte_idx = 25). move => HB25. rewrite HB25. simplify. smt (@SmtMap add_2_neq).
      move => HB25. case (byte_idx = 26). move => HB26. rewrite HB26. simplify. smt (@SmtMap add_2_neq).
      move => HB26. case (byte_idx = 27). move => HB27. rewrite HB27. simplify. smt (@SmtMap add_2_neq).
      move => HB27. case (byte_idx = 28). move => HB28. rewrite HB28. simplify. smt (@SmtMap add_2_neq).
      move => HB28. case (byte_idx = 29). move => HB29. rewrite HB29. simplify. smt (@SmtMap add_2_neq).
      move => HB29. case (byte_idx = 30). move => HB30. rewrite HB30. simplify. smt (@SmtMap add_2_neq).
      move => HB30. case (byte_idx = 31). move => HB31. rewrite HB31. simplify. smt (@SmtMap add_neq).
      move => HB31. smt ().
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
      pose z := 31 - y.
      have H_z_lower: 0 <= z by smt ().
      have H_z_upper: z < 32 by smt ().
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff).
      rewrite Map.get_set_neqE. smt(@Utils).
      reflexivity.
    qed.

lemma swap_aux1 (a b: uint256):
    a <= b => b < a + W256.of_int 32 => b = a + W256.of_int (W256.to_uint (b-a)).
    proof.
      progress.
      smt (@W256).
  qed.

lemma swap_aux2 (a b: uint256):
    a <= b => b < a + W256.of_int 32 => 0 <= W256.to_uint (b-a) < 32.
    proof.
      progress.
      smt (@W256).
      smt (@W256).
    qed.

(* lemma swap_aux3 (idx idx2 x: uint256):
    W256.of_int 32 <= idx2 - idx => W256.of_int 32 <= idx - idx2 =>
    idx <= x < idx + W256.of_int 32 =>
    forall (i: int), 0 <= i < 32 => x <> idx2 + (W256.of_int i).
    progress.
    smt(@W256 @Utils). *)
    
lemma store_store_swap_diff (memory: mem) (idx idx2 val val2: uint256):
    W256.of_int 32 <= idx2 - idx => W256.of_int 32 <= idx - idx2 =>
    store (store memory idx val) idx2 val2 = store (store memory idx2 val2) idx val.
    proof.
      progress.
      rewrite storeE storeE storeE storeE.
      progress.
      apply Map.map_eqP. progress.
      case (x = idx). progress. do 63! (rewrite Map.get_set_neqE; first smt(@Utils)). rewrite Map.get_set_sameE. do 31! (rewrite Map.get_set_neqE; first smt(@Utils)). rewrite Map.get_set_sameE. reflexivity.
      progress. case (x = idx + W256.of_int 1). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 30! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 30! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 2). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 29! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 29! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 3). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 28! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 28! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 4). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 27! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 27! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 5). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 26! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 26! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 6). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 25! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 25! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 7). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 24! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 24! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 8). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 23! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 23! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 9). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 22! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 22! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 10). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 21! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 21! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 11). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 20! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 20! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 12). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 19! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 19! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 13). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 18! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 18! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 14). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 17! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 17! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 15). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 16! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 16! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 16). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 15! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 15! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 17). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 14! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 14! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 18). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 13! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 13! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 19). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 12! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 12! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 20). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 11! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 11! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 21). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 10! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 10! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 22). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 9! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 9! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 23). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 8! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 8! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 24). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 7! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 7! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 25). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 6! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 6! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 26). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 5! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 5! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 27). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 4! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 4! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 28). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 3! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 3! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 29). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 2! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 2! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 30). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      rewrite Map.get_set_neqE; first exact add_2_neq. rewrite Map.get_set_sameE.
      rewrite Map.get_set_neqE; first exact add_2_neq. rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx + W256.of_int 31). progress.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      rewrite Map.get_set_sameE.
      rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2). progress. do 31! (rewrite Map.get_set_neqE; first smt(@Utils)). rewrite Map.get_set_sameE. do 63! (rewrite Map.get_set_neqE; first smt(@Utils)). rewrite Map.get_set_sameE. reflexivity.
      progress. case (x = idx2 + W256.of_int 1). progress.
      do 30! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 30! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 2). progress.
      do 29! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 29! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 3). progress.
      do 28! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 28! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 4). progress.
      do 27! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 27! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 5). progress.
      do 26! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 26! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 6). progress.
      do 25! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 25! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 7). progress.
      do 24! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 24! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 8). progress.
      do 23! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 23! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 9). progress.
      do 22! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 22! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 10). progress.
      do 21! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 21! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 11). progress.
      do 20! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 20! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 12). progress.
      do 19! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 19! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 13). progress.
      do 18! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 18! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 14). progress.
      do 17! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 17! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 15). progress.
      do 16! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 16! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 16). progress.
      do 15! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 15! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 17). progress.
      do 14! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 14! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 18). progress.
      do 13! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 13! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 19). progress.
      do 12! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 12! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 20). progress.
      do 11! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 11! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 21). progress.
      do 10! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 10! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 22). progress.
      do 9! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 9! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 23). progress.
      do 8! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 8! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 24). progress.
      do 7! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 7! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 25). progress.
      do 6! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 6! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 26). progress.
      do 5! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 5! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 27). progress.
      do 4! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 4! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 28). progress.
      do 3! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 3! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 29). progress.
      do 2! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      do 2! (rewrite Map.get_set_neqE; first exact add_2_neq). rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 30). progress.
      rewrite Map.get_set_neqE; first exact add_2_neq. rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      rewrite Map.get_set_neqE; first exact add_2_neq. rewrite Map.get_set_sameE.
      reflexivity.
      progress. case (x = idx2 + W256.of_int 31). progress.
      rewrite Map.get_set_sameE.
      do 31! (rewrite Map.get_set_neqE; first exact add_2_neq_of_diff). rewrite Map.get_set_neqE. smt(add_neq_of_diff).
      rewrite Map.get_set_sameE.
      reflexivity.
      progress. smt (@W256 @Map).
    qed.
      
  lemma store_store_same (memory: mem) (idx val val2):
      store (store memory idx val2) idx val = store memory idx val.
      proof.
        rewrite storeE storeE storeE.
        progress.
        smt (@Map).
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
