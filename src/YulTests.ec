pragma Goals:printall.
prover timeout=100.

require import AllCore.
require import Array.
require import ExtractedTests.
require import Int.
require import IntDiv.
require import Memory.
require import Real.
require import UInt256.
require import YulPrimops.
require import PurePrimops.
require import Utils.
require import JUtils.

import MemoryMap.

lemma is_even_correcteness (x: uint256) :
hoare [ YulTest.is_even : arg = x ==> (
    x %% W256.of_int 2 = W256.zero => res = W256.one
      ) /\ (x %% W256.of_int 2 <> W256.zero => res = W256.zero) ].
    proof.
      proc.
      wp. skip. progress. smt.
      smt.
    qed.
  
lemma writeReadTest_correctness :

    forall (address value: uint256),
phoare [ YulTest.writeReadTest :
      arg = (address, value) ==>
      res = value] = 1%r.
proof.
    progress.
  proc.
  exists* Primops.memory.
  elim*=>memory_pre.
  wp.
  call (ConcretePrimops.mload_pspec (PurePrimops.mstore memory_pre address value) address).
  call (ConcretePrimops.mstore_pspec memory_pre address value).
  skip.
  progress.
  apply load_store_same.
qed.
  
lemma revert_if_two_correctness (x : uint256) :
    phoare [YulTest.revert_if_two : arg = x /\ !Primops.reverted ==>
      (res = x + (W256.of_int 3)/\ x <> (W256.of_int 2) /\ !Primops.reverted) \/ (x = (W256.of_int 2) /\ Primops.reverted)] = 1%r.
        proc.
        inline Primops.revert.
        wp.
        skip.
        progress.
        rewrite /bool_of_uint256 /eq_uint256 in H0.
        have H1 : x{hr} + (of_int 3)%W256 = (of_int 5)%W256. smt ().
        rewrite (eq_sub_of_add_eq _ _ _ H1).
        progress.
        left.
        rewrite /bool_of_uint256 /eq_uint256 in H0.
        have H1 : x{hr} + (of_int 3)%W256 <> (of_int 5)%W256. smt (@W256).
        have H2 := neq_sub_of_add_neq _ _ _ H1.
        progress.
  qed.

lemma shifty_correctness (x s : uint256) :
    phoare [YulTest.shifty : arg = (x, s) /\ !Primops.reverted ==>
      (res = x /\ !Primops.reverted) \/ ((W256.of_int 256) < s /\ Primops.reverted)] = 1%r.
        proc.
        case ((W256.of_int 256) < s).
        rcondt 1.
        skip. progress.
        rewrite /bool_of_uint256 /gt_uint256. by smt (@W256).
        inline Primops.revert.
        wp.
        skip.
        by progress.
        rcondf 1.
        skip. progress.
        rewrite /bool_of_uint256 /gt_uint256. by smt (@W256).
        wp. skip. progress. 
        left.
        split; first last.
        exact H.
        rewrite /shr /shl.
        pose sh := to_uint s{hr}.
        pose sh' := to_uint ((W256.of_int 256) - s{hr}).
        rewrite W256.shrl_andmaskN. smt (@W256).
    case (to_uint s{hr} = 256).
        progress.
        rewrite /sh H1.
        pose v := x{hr}.
        have H2 : v `<<<` 256 = W256.zero. smt (@W256).
        have H3 : forall (s : int), W256.zero `>>>` s = W256.zero. progress. smt (@W256).
        have H4 : sh' = 0. smt (@W256).
        rewrite H2 H3 H4. simplify.
        smt (@W256).
        progress.
        rewrite W256.shlw_shrw_shlw. rewrite /sh.
        have H5 := (W256.to_uint_cmp s{hr}).
        simplify. progress.
        smt ().
        smt (@W256).
        simplify.
        rewrite shl_zero.
        have H6 : sh' = 256 - sh. smt.
        rewrite -H6.
        have H7 : x{hr} `&` (W256.masklsb sh') = (splitMask (W256.masklsb sh') x{hr}).`1. smt ().
        have H8 : x{hr} `&` (W256.invw (W256.masklsb sh')) = (splitMask (W256.masklsb sh') x{hr}).`2. smt ().
        rewrite H7 H8.
        exact W256.splitMask_add.
  qed.  
  
lemma mod_test_correctness (m : uint256) :
    phoare [YulTest.mod_test : arg = m /\ W256.one < m ==> res = W256.zero] = 1%r.
    proc.
    wp.
    skip.
    rewrite /PurePrimops.mulmod /PurePrimops.addmod.
    progress.
    have H0 : to_uint (m{hr} - W256.one) = (to_uint m{hr}) - 1. rewrite W256.to_uintB. smt (@W256). smt (@W256).
    rewrite H0.
    pose modu := to_uint m{hr}.
    have H1 : (modu - 1) * (modu - 1) = modu * (modu - 2) + 1. smt ().
    have H2 : (modu * (modu - 2) + 1) %% modu = 1. rewrite mul_add_mod_eq /modu. smt (@W256). smt (@W256).
    rewrite H1 H2.
    simplify.
    smt (@W256).
  qed.
  
lemma keccak_correctness (addr1 addr2 sz : uint256) : equiv [Primops.keccak256 ~ Primops.keccak256 : arg{1} = (addr1, sz) /\ arg{2} = (addr2, sz) /\ forall (i : uint256), W256.zero <= i /\ i < sz => Primops.memory{1}.[addr1 + i] = Primops.memory{2}.[addr2 + i] ==> res{1} = res{2}].
    proc.
    wp. skip.
    progress.
    congr.
    apply eq_from_get.
    smt (@Array).
    rewrite Array.size_offun.
    progress.
    have H_i: i < to_uint size{1} by smt(@W256).
    rewrite Array.offunE. smt ().
    rewrite Array.offunE. smt ().
    progress.
    apply H.
    smt (@W256).
  qed.

lemma splitMask_zero mask: W256.splitMask mask W256.zero = (W256.zero, W256.zero).
    proof.
      by smt(@W256).
  qed.

lemma zero_shl s: W256.zero `<<<` s = W256.zero.
    proof.
      by smt(@W256).
    qed.

lemma zero_shr s: W256.zero `>>>` s = W256.zero.
    proof.
      by smt(@W256).
    qed.

    hint simplify splitMask_zero, zero_shl, zero_shr.

lemma mstore8_test_correctness (a b: uint256): hoare[
    YulTest.mstore8test :
      arg = (a,b) /\ a < W256.of_int 256 /\ b < W256.of_int 256 ==> res = ((a `<<<` 8) `|` b) `<<<` 240
    ].
    proof.
      proc.

      inline *.
      wp.
      skip.
      progress.
      rewrite loadE storeE.
      simplify.
      do 32! rewrite W32u8.get_zero.
      apply W256.ext_eq.
      progress.
      rewrite W32u8.pack32wE. smt ().
      have H_256: 0 <= x0 && x0 < 256 by smt ().
      rewrite H_256. progress.
      pose byte_idx := x0 %/ 8.
      pose bit_idx := x0 %% 8.
    case (x0 < 240).
      progress.
      have H_lhs: !(0 <= x0 - 240 && x0 - 240 < 256) by smt ().
      rewrite H_lhs. progress.
      have H_byte_idx_low: 0 <= byte_idx by smt ().
      have H_byte_idx_high: byte_idx < 30 by smt ().
      rewrite W32u8.Pack.initE.
      have H_byte_idx_wide_range: 0 <= byte_idx && byte_idx < 32 by smt ().
      rewrite H_byte_idx_wide_range.
      progress. 
      pose idx' := 31 - byte_idx.
      have H_idx'_low: 2 <= idx' by smt ().
      have H_idx'_high: idx' < 32 by smt ().
      rewrite Map.get_set_neqE. smt.
      rewrite Map.get_set_neqE. smt.
      have H_y : y{hr}.[x0-240] = false by smt (@W256).
      rewrite H_y.
      rewrite - (W8.zerowE (bit_idx)).
      congr.
      have H_diff: forall (i j: int), 0 <= i < 32 => 0 <= j < 32 => i <> j => W256.of_int i <> W256.of_int j.
      progress.
      smt.
      smt (Map.get_set_sameE Map.get_set_neqE).
      progress.
      rewrite W32u8.Pack.initE.
    case (byte_idx = 30). progress.
      rewrite H4.
      progress.
      have H_x0: 240 <= x0 < 248 by smt ().
      have H_x0_range: (0 <= x0 - 240 && x0 - 240 < 256) by smt ().
      rewrite H_x0_range. progress.
      rewrite W256.get_out. smt ().
      rewrite Map.get_set_sameE.
      have H_lhs: 0 <= x0 && x0 < 256 by smt().
      simplify.
      have H_bit_idx: bit_idx = x0-240 by smt().
      rewrite - H_bit_idx.
      smt.
    case (byte_idx = 31). progress.
      rewrite H4.
      progress.
      have H_x0: 248 <= x0 < 256 by smt().
      have H_small: forall (a: uint256) (b: int), a < W256.of_int 256 => 8 <= b => a.[b] = false.
      progress.
      pose a8 := W8.of_int (W256.to_uint a).
      have H_a8: forall (i: int), a.[i] = a8.[i] by smt.
      rewrite H_a8. smt.
      rewrite (H_small (y{hr})). assumption. smt (). simplify.
      have H_lhs: (0 <= x0 - 240 && x0 - 240 < 256) by smt().
      rewrite H_lhs. simplify.
      rewrite Map.get_set_neqE. smt (@W256).
      rewrite (Map.get_set_sameE _ W256.zero).
      have H_bit_idx: bit_idx = x0 - 248 by smt ().
      rewrite -H_bit_idx.
      smt.
      smt ().
    qed.

lemma modexp_test_correctness (a b c: uint256): hoare [ YulTest.modexp_test: arg = (a, b, c) ==> res = (W256.one, (
    W256.of_int (
            ((W256.to_uint a) ^ (W256.to_uint b)) %% (W256.to_uint c)
    )
  ))].
      proc.
      exists* Primops.memory.
      elim*. progress.
      pose mem_1 := PurePrimops.mstore memory W256.zero (W256.of_int 32).
      pose mem_2 := PurePrimops.mstore mem_1 (W256.of_int 32) (W256.of_int 32).
      pose mem_3 := PurePrimops.mstore mem_2 (W256.of_int 64) (W256.of_int 32).
      pose mem_4 := PurePrimops.mstore mem_3 (W256.of_int 96) a.
      pose mem_5 := PurePrimops.mstore mem_4 (W256.of_int 128) b.
      pose mem_6 := PurePrimops.mstore mem_5 (W256.of_int 160) c.
      have H_mem6_get0: PurePrimops.mload mem_6 W256.zero = W256.of_int 32.
      do 5! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
      rewrite load_store_same. reflexivity.
      have H_mem6_get32: PurePrimops.mload mem_6 (W256.of_int 32) = W256.of_int 32.
      do 4! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
      rewrite load_store_same. reflexivity.
      have H_mem6_get64: PurePrimops.mload mem_6 (W256.of_int 64) = W256.of_int 32.
      do 3! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
      rewrite load_store_same. reflexivity.
      have H_mem6_get96: PurePrimops.mload mem_6 (W256.of_int 96) = a.
      do 2! ((rewrite load_store_diff; first smt(@W256)); first smt(@W256)).
      rewrite load_store_same. reflexivity.
      have H_mem6_get128: PurePrimops.mload mem_6 (W256.of_int 128) = b.
      rewrite load_store_diff. smt(@W256). smt(@W256).
      rewrite load_store_same. reflexivity.
      have H_mem6_get160: PurePrimops.mload mem_6 (W256.of_int 160) = c.
      rewrite load_store_same. reflexivity.
      seq 6 : (Primops.memory = mem_6 /\ x = a /\ y = b /\ z = c).
      call (ConcretePrimops.mstore_spec mem_5 (W256.of_int 160) c).
      call (ConcretePrimops.mstore_spec mem_4 (W256.of_int 128) b).
      call (ConcretePrimops.mstore_spec mem_3 (W256.of_int 96) a).
      call (ConcretePrimops.mstore_spec mem_2 (W256.of_int 64) (W256.of_int 32)).
      call (ConcretePrimops.mstore_spec mem_1 (W256.of_int 32) (W256.of_int 32)).
      call (ConcretePrimops.mstore_spec memory W256.zero (W256.of_int 32)).
      skip. by progress.
      inline Primops.staticcall.
      sp.
      rcondt 1. skip. by progress.
      rcondt 4.
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 64)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 32)).
      call (ConcretePrimops.mload_spec mem_6 W256.zero).
      skip. progress.
      seq 6: (
        #pre /\
        bsize = W256.of_int 32 /\
        esize = W256.of_int 32 /\
        msize = W256.of_int 32 /\
        base = a /\
        exp = b /\
        mod = c
      ).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 160)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 128)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 96)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 64)).
      call (ConcretePrimops.mload_spec mem_6 (W256.of_int 32)).
      call (ConcretePrimops.mload_spec mem_6 W256.zero).
          skip. progress.
          pose result := (W256.of_int ((W256.to_uint a) ^ (W256.to_uint b) %% (W256.to_uint c))).
          pose mem_7 := PurePrimops.mstore mem_6 W256.zero result.
          wp.
          call (ConcretePrimops.mload_spec mem_7 W256.zero).
          wp.
          call (ConcretePrimops.mstore_spec mem_6 W256.zero result).
          skip. progress.
          rewrite /mem_7.
          rewrite load_store_same.
          reflexivity.
      qed.


      
lemma calldata_test_correctness (ind : uint256) :
    phoare [YulTest.calldata_test : arg = ind ==> res = W256.one] = 1%r.
    proc.
    inline Primops.calldataload.
    wp.
    skip.
    progress.
    smt ().
  qed.

lemma aux_range (x: int): 0<=x<32 => !(W256.of_int 64 <= W256.of_int (31 - x)).
    proof.
      progress.
      smt.
    qed.

lemma aux_range2 (x: int): 0<=x<32 => !(W256.of_int 64 <= W256.of_int (63 - x)).
    proof.
      progress.
      smt.
  qed.

lemma ret_test_correctness (a b: uint256) :
    phoare [
      YulTest.ret_test :
      arg = (a,b) ==>
      load Primops.ret_data W256.zero = a /\
      load Primops.ret_data (W256.of_int 32) = b
    ] = 1%r.
    proof.
      proc.
      exists* Primops.memory.
      elim*.
      progress.
      inline *. wp.
      skip.
      progress.
      rewrite /load.
      apply W256.ext_eq.
      progress.
      rewrite pack32wE. by trivial.
      rewrite W32u8.Pack.initE.
      have H_in_range: 0 <= x %/ 8 && x %/ 8 < 32 by smt ().
      rewrite H_in_range. progress.
      rewrite Map.offunE. progress.
      have H_in_range2: !(W256.of_int 64 <= W256.of_int (31 - x %/ 8)).
      apply (aux_range (x %/ 8)). by trivial.
      rewrite H_in_range2. progress.
      rewrite /store. progress.
      have H_diff: forall (i j: int), 0<=i<32 => 32<=j<64 => W256.of_int i <> W256.of_int j.
      progress. smt.
      pose byte_idx:= 31 - x %/ 8.
      have H_byte_idx: 0<=byte_idx<32 by smt ().
      do 32! (rewrite Map.get_set_neqE; first exact H_diff).
      have H_a: (load (store Primops.memory{hr} W256.zero a{hr}) W256.zero).[x] = a{hr}.[x] by smt (load_store_same).
      rewrite- H_a.
      rewrite /byte_idx.
      rewrite /load /store.
      rewrite pack32wE. by trivial.
      rewrite W32u8.Pack.initE.
      rewrite H_in_range. simplify. by trivial.
      pose mem_1:= store Primops.memory{hr} W256.zero a{hr}.
      have H_b: load (store mem_1 (W256.of_int 32) b{hr}) (W256.of_int 32) = b{hr} by exact load_store_same.
      rewrite -H_b.
      rewrite /load.
      pose mem := store mem_1 (W256.of_int 32) b{hr}.
      have H_inner: forall (i: int), 0<=i<32 =>
        ((Map.offun (fun (i0: uint256) => (
          if W256.of_int 64 <= i0
          then witness
          else (store mem_1 (W256.of_int 32) (pack32_t (W32u8.Pack.init (fun (i1: int) => mem.[W256.of_int (63-i1)])))).[i0]
            ))).[W256.of_int (63-i)] = mem.[W256.of_int (63-i)]).
                progress.
                rewrite Map.offunE. progress.
                have H_if: !(W256.of_int 64 <= W256.of_int (63-i)). smt.
                rewrite H_if. progress.
                rewrite /mem /store. progress.
                smt.
                apply W256.ext_eq. progress.
                rewrite pack32wE. trivial.
                rewrite initE.
                have H_range: 0 <= x %/ 8 && x %/ 8 < 32 by smt ().
                rewrite H_range. progress.
                rewrite Map.offunE. progress.
                have H_range': !(W256.of_int 64 <= W256.of_int (63 - x %/ 8)) by exact aux_range2.
                rewrite H_range'. progress.
                rewrite /store. progress.
                rewrite pack32wE. by trivial.
                rewrite initE.
                rewrite H_range. progress.
                congr.
                pose idx := x %/ 8.
                have H_diff: forall (i j: int), 32<=i<64 => 32<=j<64 => i <> j => W256.of_int i <> W256.of_int j.
                progress. smt.
                smt (Map.get_set_sameE Map.get_set_neqE).
      qed.      

