pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

op topoint (p : F * F) : (int * int) = (ZModField.asint (fst p), ZModField.asint (snd p)).

module PointAddIntoDest = {
  proc low(p1, p2, dest) =
  {
    var _1, _5, _6, _9, _13, _14;
    _1 <@ Primops.mload(p1);
    Primops.mstore(W256.of_int 0, _1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    _6 <@ Primops.mload(p2);
    Primops.mstore(W256.of_int 64, _6);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
    {
      RevertWithMessage.low((W256.of_int 30), (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*)));
    }
  }

  proc low'(p1, p2, dest) =
  {
    var _1, _5, _6, _9, _13, _14;
    _1 <@ Primops.mload(p1);
    _5 <@ Primops.mload(p1 + W256.of_int 32);
    _6 <@ Primops.mload(p2);
    _9 <@ Primops.mload(p2 + W256.of_int 32);
    Primops.mstore(W256.of_int 0, _1);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, _6);
    Primops.mstore(W256.of_int 96, _9);
    _13 <@ Primops.gas();
    _14 <@ Primops.staticcall(_13, W256.of_int 6, W256.zero, W256.of_int 128, dest, W256.of_int 64);
    if ((bool_of_uint256 (PurePrimops.iszero _14)))
    {
      RevertWithMessage.low((W256.of_int 30), (W256.of_int STRING (*pointAddIntoDest: ecAdd failed*)));
    }
  }

  proc mid(x1 : int, y1 : int, x2 : int, y2 : int) : (int * int) option = {
    var x1_F, x2_F, y1_F, y2_F, result;
      x1_F <- ZModField.inzmod x1;
      y1_F <- ZModField.inzmod y1;
      x2_F <- ZModField.inzmod x2;
      y2_F <- ZModField.inzmod y2;
      result <- ecAdd_precompile x1_F y1_F x2_F y2_F;
      return (omap topoint result);
  }
}.

lemma pointAddIntoDest_pspec_revert :
phoare [ PointAddIntoDest.low : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; inline*; wp; by progress. qed.

lemma pointAddIntoDest_extracted_equiv_low : equiv [
    Verifier_1261.usr_pointAddIntoDest ~ PointAddIntoDest.low :
      ={arg, glob PointAddIntoDest} ==>
      ={res, glob PointAddIntoDest}
    ].
proof.
  proc.
  seq 24 10: (#pre /\ ={_14}).
  inline*. wp. skip. by progress.
  inline*. wp. skip. by progress.
qed.

lemma uint256_eq (a : uint256) : a = - (- a).
    smt (@W256).
  qed.

lemma uint256_zero_sub_eq_sub (a : uint256) : W256.zero - a = - a.
    smt (@W256).
  qed.

lemma uint256_sub_distr2 (a b c : uint256) : a - (b + c) = (a - c) - b.
    smt (@W256).
  qed.
  
lemma uint256_ord3' (a b : uint256) : W256.zero < a => a < - b => b < - a.
    progress.
    rewrite (uint256_eq b).
    apply uint256_ord3.
    exact H.
    exact H0.
  qed.
  
lemma usr_pointAddIntoDest_low_matches_low' (p1 p2 dest_address : uint256) : equiv [
    PointAddIntoDest.low ~ PointAddIntoDest.low':
      ={arg, glob PointAddIntoDest} /\
      arg{1} = (p1, p2, dest_address) /\
        W256.of_int 128 < p1 /\ W256.of_int 128 < - p1 /\
        W256.of_int 128 < (p1 + W256.of_int 32) /\ W256.of_int 128 < -(p1 + W256.of_int 32) /\
        W256.of_int 128 < p2 /\ W256.of_int 128 < - p2 /\
        W256.of_int 128 < (p2 + W256.of_int 32) /\ W256.of_int 128 < -(p2 + W256.of_int 32)
      ==>
      ={res, glob PointAddIntoDest}
    ].
    proof.
      exists* Primops.memory{1}.
      elim*=> memory.
      exists* (PurePrimops.mload memory p1).
      elim*=>x1.
      exists* (PurePrimops.mload memory (p1 + W256.of_int 32)).
      elim*=>y1.
      exists* (PurePrimops.mload memory p2).
      elim*=>x2.
      exists* (PurePrimops.mload memory (p2 + W256.of_int 32)).
      elim*=>y2.
      proc.
      sim.
      seq 9 9 :
    (
      y2 = (PurePrimops.mload memory (p2 + (W256.of_int 32))) /\
      x2 = (PurePrimops.mload memory p2) /\
      y1 = (PurePrimops.mload memory (p1 + (W256.of_int 32))) /\
      x1 = (PurePrimops.mload memory p1) /\
      ={Primops.memory} /\ ={dest} /\ ={Primops.reverted} /\ dest{1} = dest_address /\ ={_13} /\
      Primops.memory{1} =
      PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory W256.zero x1) (W256.of_int 32) y1) (W256.of_int 64) x2) (W256.of_int 96) y2 /\
      (of_int 128)%W256 < p1 /\
      (of_int 128)%W256 < -p1 /\
      (of_int 128)%W256 < p1 + (of_int 32)%W256 /\
      (of_int 128)%W256 < - (p1 + (of_int 32)%W256) /\
      (of_int 128)%W256 < p2 /\
      (of_int 128)%W256 < -p2 /\
      (of_int 128)%W256 < p2 + (of_int 32)%W256 /\
      (of_int 128)%W256 < - (p2 + (of_int 32)%W256)
    ).
        inline Primops.mload Primops.mstore Primops.gas.
        wp. skip. progress.

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        apply uint256_ord1.
        smt (@W256 @Utils). smt (@W256 @Utils).

        apply uint256_ord2'.
        smt (@W256 @Utils).
    
    
        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils).
        rewrite uint256_zero_sub_eq_sub.
        smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        apply uint256_ord1.
        smt (@W256 @Utils). smt (@W256 @Utils). rewrite uint256_sub_distr2.
        have J : (of_int 64)%W256 - (of_int 32)%W256 = (of_int 32)%W256. smt (@W256).
        rewrite J.
        apply uint256_ord2'.
        smt (@W256 @Utils).
    
        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). rewrite uint256_sub_distr2. 
        have J : (of_int 32)%W256 - (of_int 32)%W256 = W256.zero. smt (@W256).
        rewrite J.
        rewrite uint256_zero_sub_eq_sub.
        smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). rewrite uint256_zero_sub_eq_sub. smt (@W256 @Utils).

        reflexivity.

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). rewrite uint256_zero_sub_eq_sub. smt (@W256 @Utils). 
    
        rewrite MemoryMap.load_store_diff.
        apply uint256_ord1.
        smt (@W256 @Utils). smt (@W256 @Utils).
        apply uint256_ord2'. smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). rewrite uint256_zero_sub_eq_sub. smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        apply uint256_ord1.
        smt (@W256 @Utils). smt (@W256 @Utils). rewrite uint256_sub_distr2.
        have J : (of_int 64)%W256 - (of_int 32)%W256 = (of_int 32)%W256. smt (@W256).
        rewrite J.
        apply uint256_ord2'.
        smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). rewrite uint256_sub_distr2. 
        have J : (of_int 32)%W256 - (of_int 32)%W256 = W256.zero. smt (@W256).
        rewrite J.
        rewrite uint256_zero_sub_eq_sub.
        smt (@W256 @Utils). 

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). rewrite uint256_zero_sub_eq_sub. smt (@W256 @Utils).

        reflexivity.

        exists* Primops.memory{1}.
        elim*=> memory'.

        call {1} (ConcretePrimops.staticcall_ec_add_pspec memory' (x1, y1) (x2, y2) W256.zero dest_address).
        call {2} (ConcretePrimops.staticcall_ec_add_pspec memory' (x1, y1) (x2, y2) W256.zero dest_address).

        skip. progress.


        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_same.
        reflexivity.
    
        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_same.
        reflexivity.
   
        rewrite MemoryMap.load_store_diff.
        smt (@W256 @Utils). smt (@W256 @Utils).

        rewrite MemoryMap.load_store_same.
        reflexivity.

        rewrite MemoryMap.load_store_same.
        reflexivity.

        smt ().

        smt ().
  qed.

lemma exists_of_is_some ['a] (ov : 'a option) : is_some ov => exists (v : 'a), ov = Some v. progress. smt. qed.

lemma PointAddIntoDest_mid_of_low' (x1v x2v y1v y2v : int) (p1v p2v destv : uint256) (memory0 : MemoryMap.mem) : equiv [
    PointAddIntoDest.low' ~ PointAddIntoDest.mid :
    0 <= x1v < p /\ 0 <= x2v < p /\ 0 <= y1v < p /\ 0 <= y2v < p /\
    Primops.memory{1} = memory0 /\
    PurePrimops.mload memory0 p1v = W256.of_int x1v /\
    PurePrimops.mload memory0 (p1v + W256.of_int 32) = W256.of_int y1v /\
    PurePrimops.mload memory0 p2v = W256.of_int x2v /\
    PurePrimops.mload memory0 (p2v + W256.of_int 32) = W256.of_int y2v /\
      arg{1} = (p1v, p2v, destv) /\ arg{2} = (x1v, y1v, x2v, y2v) /\ !Primops.reverted{1}
      ==>
        exists (memory_F : MemoryMap.mem),
      memory_F = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero (W256.of_int x1v)) (W256.of_int 32) (W256.of_int y1v)) (W256.of_int 64) (W256.of_int x2v)) (W256.of_int 96) (W256.of_int y2v) /\
      (
        ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int x2v, W256.of_int y2v) /\
        exists (x y : F),
        ecAdd_precompile (ZModField.inzmod x1v) (ZModField.inzmod y1v) (ZModField.inzmod x2v) (ZModField.inzmod y2v) = Some (x, y) /\
        res{2} = Some (ZModField.asint x, ZModField.asint y) /\
        Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory_F destv (W256.of_int (ZModField.asint x))) (destv + W256.of_int 32) (W256.of_int (ZModField.asint y)) /\
        !Primops.reverted{1}
      ) \/
      (
        !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int x2v, W256.of_int y2v) /\
        res{2} = None /\
        Primops.reverted{1}
      )
    ]. proof.
        proc.
        seq 4 0 :
    (
      #pre /\
      _1{1} = W256.of_int x1v /\
      _5{1} = W256.of_int y1v /\
      _6{1} = W256.of_int x2v /\
      _9{1} = W256.of_int y2v
    ).
    inline *. wp. skip. progress.
    seq 5 0 : 
    (
      0 <= x1v < p /\ 0 <= x2v < p /\ 0 <= y1v < p /\ 0 <= y2v < p /\
      (p1{1}, p2{1}, dest{1}) = (p1v, p2v, destv) /\
      (x1{2}, y1{2}, x2{2}, y2{2}) = (x1v, y1v, x2v, y2v) /\
    _1{1} = (of_int x1v)%W256 /\
    _5{1} = (of_int y1v)%W256 /\
    _6{1} = (of_int x2v)%W256 /\
    _5{1} = (of_int y1v)%W256 /\
    _9{1} = (of_int y2v)%W256 /\
    dest{1} = destv /\  
    Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero _1{1}) (W256.of_int 32) _5{1}) (W256.of_int 64) _6{1}) (W256.of_int 96) _9{1} /\ !Primops.reverted{1}
    ).
        inline *. wp. skip. progress.
        exists* Primops.memory{1}.
        elim*=> memory_F.

        seq 1 0 :
    (
      0 <= x1v < p /\ 0 <= x2v < p /\ 0 <= y1v < p /\ 0 <= y2v < p /\
      (p1{1}, p2{1}, dest{1}) = (p1v, p2v, destv) /\
      (x1{2}, y1{2}, x2{2}, y2{2}) = (x1v, y1v, x2v, y2v) /\
      _1{1} = (of_int x1v)%W256 /\
      _5{1} = (of_int y1v)%W256 /\
      _6{1} = (of_int x2v)%W256 /\
      _9{1} = (of_int y2v)%W256 /\
      dest{1} = destv /\
      memory_F = PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore (PurePrimops.mstore memory0 W256.zero _1{1}) (W256.of_int 32) _5{1}) (W256.of_int 64) _6{1}) (W256.of_int 96) _9{1} /\
        !Primops.reverted{1} /\
      (
        (_14{1} = W256.zero /\ !ConcretePrimops.staticcall_ec_add_should_succeed (_1{1}, _5{1}) (_6{1}, _9{1}) /\ Primops.memory{1} = memory_F) \/
        (
          _14{1} = W256.one /\ ConcretePrimops.staticcall_ec_add_should_succeed (_1{1}, _5{1}) (_6{1}, _9{1}) /\
          Primops.memory{1} =
          PurePrimops.mstore
          (PurePrimops.mstore
            memory_F
            destv
            (ConcretePrimops.ecAdd_precompile_unsafe_cast (W256.of_int x1v, W256.of_int y1v) (W256.of_int x2v, W256.of_int y2v)).`1
          )
          (destv + W256.of_int 32)
          (ConcretePrimops.ecAdd_precompile_unsafe_cast (W256.of_int x1v, W256.of_int y1v) (W256.of_int x2v, W256.of_int y2v)).`2
        )
      )
    ).
        call {1} (ConcretePrimops.staticcall_ec_add_pspec memory_F (W256.of_int x1v, W256.of_int y1v) (W256.of_int x2v, W256.of_int y2v) W256.zero destv).
        skip. progress.

        rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
        rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
        rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
        rewrite MemoryMap.load_store_same. reflexivity.

        rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
        rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
        rewrite MemoryMap.load_store_same. reflexivity.

        rewrite MemoryMap.load_store_diff. smt (@W256). smt (@W256).
        rewrite MemoryMap.load_store_same. reflexivity.

        rewrite MemoryMap.load_store_same. reflexivity.
    
        case (ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int x1{2}, W256.of_int y1{2}) (W256.of_int x2{2}, W256.of_int y2{2})).
        progress. smt ().

        exists* _14{1}.
        elim* => sres.
    case (sres = W256.zero).
        rcondt {1} 1.
        progress. skip. progress. rewrite /iszero /bool_of_uint256. smt (@W256).
        inline RevertWithMessage.low Primops.mstore Primops.revert.
        sp. skip. progress. smt (@W256).
    have J : (ecAdd_precompile ((ZModField.inzmod x1{2})) ((ZModField.inzmod y1{2}))
      ((ZModField.inzmod x2{2})) ((ZModField.inzmod y2{2}))) = None.
        have T0 : ((of_int x1{2})%W256, (of_int y1{2})%W256).`1 = W256.of_int x1{2}. smt ().
        have T1 : ((of_int x1{2})%W256, (of_int y1{2})%W256).`2 = W256.of_int y1{2}. smt ().
        have T2 : ((of_int x2{2})%W256, (of_int y2{2})%W256).`1 = W256.of_int x2{2}. smt ().
        have T3 : ((of_int x2{2})%W256, (of_int y2{2})%W256).`2 = W256.of_int y2{2}. smt ().
        have J' : ! (ConcretePrimops.staticcall_ec_add_should_succeed
         ((of_int x1{2})%W256, (of_int y1{2})%W256)
         ((of_int x2{2})%W256, (of_int y2{2})%W256)). smt (@W256). 
           rewrite /ConcretePrimops.staticcall_ec_add_should_succeed /ConcretePrimops.point_oncurve /ConcretePrimops.point_wellformed in J'.
           simplify J'.
           rewrite T0 T1 T2 T3 in J'.
           rewrite W256.to_uint_small in J'.  progress. apply (lt_trans _ p _). exact H0. exact p_lt_W256_mod.
           have T0' : to_uint ((of_int x1{2}))%W256 = x1{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           have T1' : to_uint ((of_int y1{2}))%W256 = y1{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           have T2' : to_uint ((of_int x2{2}))%W256 = x2{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           have T3' : to_uint ((of_int y2{2}))%W256 = y2{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           have J'' : ! (on_curve
         ((ZModField.inzmod (to_uint ((of_int x1{2}))%W256)),
           (ZModField.inzmod (to_uint ((of_int y1{2}))%W256))) /\
             on_curve
         ((ZModField.inzmod (to_uint ((of_int x2{2}))%W256)),
           (ZModField.inzmod (to_uint ((of_int y2{2}))%W256))) /\
             is_some
         (ecAdd_precompile ((ZModField.inzmod x1{2}))
           ((ZModField.inzmod (to_uint ((of_int y1{2}))%W256)))
           ((ZModField.inzmod (to_uint ((of_int x2{2}))%W256)))
           ((ZModField.inzmod (to_uint ((of_int y2{2}))%W256))))).
             have INT : (of_int x1{2})%W256 = (of_int x1{2})%W256 %% (of_int p)%W256 /\
       (of_int y1{2})%W256 = (of_int y1{2})%W256 %% (of_int p)%W256 /\
       (of_int x2{2})%W256 = (of_int x2{2})%W256 %% (of_int p)%W256 /\
       (of_int y2{2})%W256 = (of_int y2{2})%W256 %% (of_int p)%W256.
         do 4! (rewrite -cast_uint256_mod_eq_of_lt; first progress; exact p_lt_W256_mod).
         progress.
         smt ().
         rewrite T1' T2' T3' in J''.
       have J''' : ! (on_curve
          ((ZModField.inzmod (to_uint ((of_int x1{2}))%W256)),
           (ZModField.inzmod y1{2}))) \/
        ! (on_curve ((ZModField.inzmod x2{2}), (ZModField.inzmod y2{2}))) \/
        ! (is_some
          (ecAdd_precompile ((ZModField.inzmod x1{2}))
             ((ZModField.inzmod y1{2})) ((ZModField.inzmod x2{2}))
             ((ZModField.inzmod y2{2})))). smt ().
               case J'''.
               smt (@EllipticCurve).
         move=>J'''.
               case J'''.
               smt (@EllipticCurve).
               smt ().

        rewrite J. smt ().

        rcondf {1} 1.
        progress. skip. progress. rewrite /iszero /bool_of_uint256. smt (@W256).
        sp. skip. progress. 
    
        exists ((PurePrimops.mstore
      ((PurePrimops.mstore
          ((PurePrimops.mstore
              ((PurePrimops.mstore memory0 W256.zero ((of_int x1{2}))%W256))
              ((of_int 32))%W256 ((of_int y1{2}))%W256))
          ((of_int 64))%W256 ((of_int x2{2}))%W256))
      ((of_int 96))%W256 ((of_int y2{2}))%W256)).
        progress. left. progress.
  
        simplify. apply cast_uint256_mod_eq_of_lt. progress. exact p_lt_W256_mod.
        simplify. apply cast_uint256_mod_eq_of_lt. progress. exact p_lt_W256_mod.
        simplify. apply cast_uint256_mod_eq_of_lt. progress. exact p_lt_W256_mod.
        simplify. apply cast_uint256_mod_eq_of_lt. progress. exact p_lt_W256_mod.
        smt ().
        smt ().
        smt ().
  have J1 : ConcretePrimops.staticcall_ec_add_should_succeed
       ((of_int x1{2})%W256, (of_int y1{2})%W256)
       ((of_int x2{2})%W256, (of_int y2{2})%W256). smt ().
  rewrite /ConcretePrimops.staticcall_ec_add_should_succeed in J1.
  have J2 : exists (p : F * F), ecAdd_precompile
         ((ZModField.inzmod (to_uint ((of_int x1{2})%W256, (of_int y1{2})%W256).`1)))
         ((ZModField.inzmod (to_uint ((of_int x1{2})%W256, (of_int y1{2})%W256).`2)))
         ((ZModField.inzmod (to_uint ((of_int x2{2})%W256, (of_int y2{2})%W256).`1)))
         ((ZModField.inzmod (to_uint ((of_int x2{2})%W256, (of_int y2{2})%W256).`2))) = Some p. apply exists_of_is_some. smt ().
   case J2.
   move=> pt.
   pose x := pt.`1.
   pose y := pt.`2.
           progress.
           exists x. exists y. progress.
           rewrite of_uintK of_uintK of_uintK of_uintK in H10.
           have J3 : (x, y) = pt. smt ().
           rewrite J3. rewrite -H10. congr.
           rewrite pmod_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           rewrite pmod_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           rewrite pmod_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           rewrite pmod_small. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod. reflexivity.
           rewrite of_uintK of_uintK of_uintK of_uintK in H10.
           rewrite pmod_small in H10. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod.
           rewrite pmod_small in H10. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod.
           rewrite pmod_small in H10. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod.
           rewrite pmod_small in H10. progress. apply (lt_trans _ p _). smt (). exact p_lt_W256_mod.
           rewrite H10 /topoint. simplify. smt ().
           have J4 : Primops.memory{1} =
         (PurePrimops.mstore
           ((PurePrimops.mstore
               ((PurePrimops.mstore
                   ((PurePrimops.mstore
                       ((PurePrimops.mstore
                           ((PurePrimops.mstore memory0 W256.zero ((of_int x1{2}))%W256))
                           ((of_int 32))%W256 ((of_int y1{2}))%W256))%PurePrimops
                       ((of_int 64))%W256 ((of_int x2{2}))%W256))%PurePrimops
                   ((of_int 96))%W256 ((of_int y2{2}))%W256))%PurePrimops dest{1}
               ((ConcretePrimops.ecAdd_precompile_unsafe_cast
                   ((of_int x1{2})%W256, (of_int y1{2})%W256)
                   ((of_int x2{2})%W256, (of_int y2{2})%W256))).`1))
           (dest{1} + (of_int 32)%W256)
           ((ConcretePrimops.ecAdd_precompile_unsafe_cast
               ((of_int x1{2})%W256, (of_int y1{2})%W256)
               ((of_int x2{2})%W256, (of_int y2{2})%W256))).`2). smt ().
                 rewrite J4. congr. congr.
                 have bla : ConcretePrimops.ecAdd_precompile_unsafe_cast ((of_int x1{2})%W256, (of_int y1{2})%W256) ((of_int x2{2})%W256, (of_int y2{2})%W256) =
         ((of_int ((ZModField.asint x)))%W256, (of_int ((ZModField.asint y)))%W256).
           rewrite /ConcretePrimops.ecAdd_precompile_unsafe_cast. simplify. rewrite H10.
           have blu : odflt (ZModField.zero, ZModField.zero) (Some pt) = pt. smt ().
           rewrite blu. smt ().
           smt (). smt ().
       qed.

