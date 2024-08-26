pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Field.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import RevertWithMessage.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

import MemoryMap.

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
      x1_F <- FieldQ.inF x1;
      y1_F <- FieldQ.inF y1;
      x2_F <- FieldQ.inF x2;
      y2_F <- FieldQ.inF y2;
      result <- ecAdd_precompile x1_F y1_F x2_F y2_F;
      return (omap F_to_int_point result);
  }

  proc high_field(p1: FieldQ.F*FieldQ.F, p2: FieldQ.F*FieldQ.F): (FieldQ.F*FieldQ.F) option = {
    return ecAdd_precompile p1.`1 p1.`2 p2.`1 p2.`2;
  }

  proc high(p1: g, p2: g): g = {
    return p1 + p2;
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
  
lemma pointAddIntoDest_low_equiv_low' (p1 p2 dest_address : uint256) : equiv [
    PointAddIntoDest.low ~ PointAddIntoDest.low':
      ={arg, glob PointAddIntoDest} /\
      arg{1} = (p1, p2, dest_address) /\
        W256.of_int 128 <= p1 /\ W256.of_int 64 <= - p1 /\
        W256.of_int 128 <= p2 /\ W256.of_int 64 <= - p2
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
      seq 9 9 :
    (
      y2 = (PurePrimops.mload memory (p2 + (W256.of_int 32))) /\
      x2 = (PurePrimops.mload memory p2) /\
      y1 = (PurePrimops.mload memory (p1 + (W256.of_int 32))) /\
      x1 = (PurePrimops.mload memory p1) /\
      ={Primops.memory} /\ ={dest} /\ ={Primops.reverted} /\ dest{1} = dest_address /\ ={_13} /\
      Primops.memory{1} =
      PurePrimops.mstore (store (store (store memory W256.zero x1) (W256.of_int 32) y1) (W256.of_int 64) x2) (W256.of_int 96) y2 /\
      (of_int 128)%W256 <= p1 /\
      (of_int 64)%W256 <= -p1 /\
      (of_int 128)%W256 <= p2 /\
      (of_int 64)%W256 <= -p2
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
        by sim.
    qed.


op pointAddIntoDest_memory_footprint (mem_0: mem) (dest: uint256) (p1 p2: int*int) (ret: FieldQ.F*FieldQ.F) =
  let mem_1 = store mem_0 W256.zero (W256.of_int p1.`1) in
  let mem_2 = store mem_1 (W256.of_int 32) (W256.of_int p1.`2) in
  let mem_3 = store mem_2 (W256.of_int 64) (W256.of_int p2.`1) in
  let mem_4 = store mem_3 (W256.of_int 96) (W256.of_int p2.`2) in
  let mem_5 = store mem_4 dest (W256.of_int(FieldQ.asint(ret.`1))) in
  store mem_5 (dest + W256.of_int 32) (W256.of_int(FieldQ.asint(ret.`2))).
  
lemma pointAddIntoDest_low'_equiv_mid (x1v x2v y1v y2v : int) (p1v p2v destv : uint256) (memory0 : MemoryMap.mem) : equiv [
    PointAddIntoDest.low' ~ PointAddIntoDest.mid :
    0 <= x1v < FieldQ.p /\ 0 <= x2v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= y2v < FieldQ.p /\
    Primops.memory{1} = memory0 /\
    PurePrimops.mload memory0 p1v = W256.of_int x1v /\
    PurePrimops.mload memory0 (p1v + W256.of_int 32) = W256.of_int y1v /\
    PurePrimops.mload memory0 p2v = W256.of_int x2v /\
    PurePrimops.mload memory0 (p2v + W256.of_int 32) = W256.of_int y2v /\
      arg{1} = (p1v, p2v, destv) /\ arg{2} = (x1v, y1v, x2v, y2v) /\ !Primops.reverted{1}
      ==>
      (
        ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int x1v, W256.of_int y1v) (W256.of_int x2v, W256.of_int y2v) /\
        exists (x y : FieldQ.F),
        ecAdd_precompile (FieldQ.inF x1v) (FieldQ.inF y1v) (FieldQ.inF x2v) (FieldQ.inF y2v) = Some (x, y) /\
        res{2} = Some (FieldQ.asint x, FieldQ.asint y) /\
        Primops.memory{1} = pointAddIntoDest_memory_footprint memory0 destv (x1v, y1v) (x2v, y2v) (x, y) /\
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
      0 <= x1v < FieldQ.p /\ 0 <= x2v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= y2v < FieldQ.p /\
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
        inline *. wp. skip. by progress.
        exists* Primops.memory{1}.
        elim*=> memory_F.

        seq 1 0 :
    (
      0 <= x1v < FieldQ.p /\ 0 <= x2v < FieldQ.p /\ 0 <= y1v < FieldQ.p /\ 0 <= y2v < FieldQ.p /\
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
    have J : (ecAdd_precompile ((FieldQ.inF x1{2})) ((FieldQ.inF y1{2}))
      ((FieldQ.inF x2{2})) ((FieldQ.inF y2{2}))) = None.
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
           rewrite W256.to_uint_small in J'.  progress. apply (lt_trans _ FieldQ.p _). exact H0. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
           have T0' : to_uint ((of_int x1{2}))%W256 = x1{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           have T1' : to_uint ((of_int y1{2}))%W256 = y1{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           have T2' : to_uint ((of_int x2{2}))%W256 = x2{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           have T3' : to_uint ((of_int y2{2}))%W256 = y2{2}. rewrite W256.to_uint_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           have J'' : ! (on_curve
         ((FieldQ.inF (to_uint ((of_int x1{2}))%W256)),
           (FieldQ.inF (to_uint ((of_int y1{2}))%W256))) /\
             on_curve
         ((FieldQ.inF (to_uint ((of_int x2{2}))%W256)),
           (FieldQ.inF (to_uint ((of_int y2{2}))%W256))) /\
             is_some
         (ecAdd_precompile ((FieldQ.inF x1{2}))
           ((FieldQ.inF (to_uint ((of_int y1{2}))%W256)))
           ((FieldQ.inF (to_uint ((of_int x2{2}))%W256)))
           ((FieldQ.inF (to_uint ((of_int y2{2}))%W256))))).
             have INT : (of_int x1{2})%W256 = (of_int x1{2})%W256 %% (of_int FieldQ.p)%W256 /\
       (of_int y1{2})%W256 = (of_int y1{2})%W256 %% (of_int FieldQ.p)%W256 /\
       (of_int x2{2})%W256 = (of_int x2{2})%W256 %% (of_int FieldQ.p)%W256 /\
       (of_int y2{2})%W256 = (of_int y2{2})%W256 %% (of_int FieldQ.p)%W256.
         do 4! (rewrite -cast_uint256_mod_eq_of_lt; first progress; rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress).
         by progress.
         smt ().
         rewrite T1' T2' T3' in J''.
       have J''' : ! (on_curve
          ((FieldQ.inF (to_uint ((of_int x1{2}))%W256)),
           (FieldQ.inF y1{2}))) \/
        ! (on_curve ((FieldQ.inF x2{2}), (FieldQ.inF y2{2}))) \/
        ! (is_some
          (ecAdd_precompile ((FieldQ.inF x1{2}))
             ((FieldQ.inF y1{2})) ((FieldQ.inF x2{2}))
             ((FieldQ.inF y2{2})))). smt ().
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
    
        left. progress.
  
        simplify. apply cast_uint256_mod_eq_of_lt. progress. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        simplify. apply cast_uint256_mod_eq_of_lt. progress. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        simplify. apply cast_uint256_mod_eq_of_lt. progress. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        simplify. apply cast_uint256_mod_eq_of_lt. progress. rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
        smt ().
        smt ().
        smt ().
  have J1 : ConcretePrimops.staticcall_ec_add_should_succeed
       ((of_int x1{2})%W256, (of_int y1{2})%W256)
       ((of_int x2{2})%W256, (of_int y2{2})%W256). smt ().
  rewrite /ConcretePrimops.staticcall_ec_add_should_succeed in J1.
  have J2 : exists (p : FieldQ.F * FieldQ.F), ecAdd_precompile
         ((FieldQ.inF (to_uint ((of_int x1{2})%W256, (of_int y1{2})%W256).`1)))
         ((FieldQ.inF (to_uint ((of_int x1{2})%W256, (of_int y1{2})%W256).`2)))
         ((FieldQ.inF (to_uint ((of_int x2{2})%W256, (of_int y2{2})%W256).`1)))
         ((FieldQ.inF (to_uint ((of_int x2{2})%W256, (of_int y2{2})%W256).`2))) = Some p. apply exists_of_is_some. smt ().
   case J2.
   move=> pt.
   pose x := pt.`1.
   pose y := pt.`2.
           progress.
           exists x. exists y. progress.
           rewrite of_uintK of_uintK of_uintK of_uintK in H10.
           have J3 : (x, y) = pt. smt ().
           rewrite J3. rewrite -H10. congr.
           rewrite pmod_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           rewrite pmod_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           rewrite pmod_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           rewrite pmod_small. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress. reflexivity.
           rewrite of_uintK of_uintK of_uintK of_uintK in H10.
           rewrite pmod_small in H10. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
           rewrite pmod_small in H10. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
           rewrite pmod_small in H10. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
           rewrite pmod_small in H10. progress. apply (lt_trans _ FieldQ.p _). smt (). rewrite -Constants.q_eq_fieldq_p /Constants.Q; by progress.
           rewrite H10. simplify. smt ().
           rewrite /pointAddIntoDest_memory_footprint. simplify.
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
         ((of_int ((FieldQ.asint x)))%W256, (of_int ((FieldQ.asint y)))%W256).
           rewrite /ConcretePrimops.ecAdd_precompile_unsafe_cast. simplify. rewrite H10.
           have blu : odflt (FieldQ.zero, FieldQ.zero) (Some pt) = pt. smt ().
           rewrite blu. smt ().
           smt (). smt ().
       qed.

     lemma pointAddIntoDest_low_equiv_mid (mem_0: mem) (p1_addr p2_addr dest_addr: uint256) (p1 p2: int*int):
     equiv [
         PointAddIntoDest.low ~ PointAddIntoDest.mid:
           arg{1} = (p1_addr, p2_addr, dest_addr) /\
         W256.of_int 128 <= p1_addr /\ W256.of_int 64 <= -p1_addr /\
         W256.of_int 128 <= p2_addr /\ W256.of_int 64 <= -p2_addr /\
         0 <= p1.`1 < FieldQ.p /\ 0 <= p1.`2 < FieldQ.p /\ 0 <= p2.`1 < FieldQ.p /\ 0 <= p2.`2 < FieldQ.p /\
         Primops.memory{1} = mem_0 /\
         W256.to_uint (load mem_0 p1_addr) = p1.`1 /\
         W256.to_uint (load mem_0 (p1_addr + W256.of_int 32)) = p1.`2 /\
         W256.to_uint (load mem_0 p2_addr) = p2.`1 /\
         W256.to_uint (load mem_0 (p2_addr + W256.of_int 32)) = p2.`2 /\
           arg{2} = (p1.`1, p1.`2, p2.`1, p2.`2) /\
         !Primops.reverted{1} ==>
           (
             ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
             exists (x y: FieldQ.F),
             ecAdd_precompile (FieldQ.inF p1.`1) (FieldQ.inF p1.`2) (FieldQ.inF p2.`1) (FieldQ.inF p2.`2) = Some (x,y) /\
             res{2} = Some (FieldQ.asint x, FieldQ.asint y) /\
             Primops.memory{1} = pointAddIntoDest_memory_footprint mem_0 dest_addr p1 p2 (x,y) /\
             !Primops.reverted{1}
           ) \/
           (
             !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
             res{2} = None /\
             Primops.reverted{1}
           )
         ].
         proof.
           transitivity PointAddIntoDest.low'
         (
           ={arg, glob PointAddIntoDest} /\
             Primops.memory{1} = mem_0 /\
             !Primops.reverted{1} /\
           arg{1} = (p1_addr, p2_addr, dest_addr) /\
           W256.of_int 128 <= p1_addr /\ W256.of_int 64 <= - p1_addr /\
           W256.of_int 128 <= p2_addr /\ W256.of_int 64 <= - p2_addr
            ==>
            ={res, glob PointAddIntoDest}
         )
         (
            0 <= p1.`1 < FieldQ.p /\ 0 <= p1.`2 < FieldQ.p /\ 0 <= p2.`1 < FieldQ.p /\ 0 <= p2.`2 < FieldQ.p /\
            Primops.memory{1} = mem_0 /\
            load mem_0 p1_addr = W256.of_int p1.`1 /\
            load mem_0 (p1_addr + W256.of_int 32) = W256.of_int p1.`2 /\
            load mem_0 p2_addr = W256.of_int p2.`1 /\
            load mem_0 (p2_addr + W256.of_int 32) = W256.of_int p2.`2 /\
           arg{1} = (p1_addr, p2_addr, dest_addr) /\
           arg{2} = (p1.`1, p1.`2, p2.`1, p2.`2) /\
           !Primops.reverted{1}
            ==>
            (
              ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
              exists (x y : FieldQ.F),
              ecAdd_precompile (FieldQ.inF p1.`1) (FieldQ.inF p1.`2) (FieldQ.inF p2.`1) (FieldQ.inF p2.`2) = Some (x, y) /\
              res{2} = Some (FieldQ.asint x, FieldQ.asint y) /\
              Primops.memory{1} = pointAddIntoDest_memory_footprint mem_0 dest_addr p1 p2 (x, y) /\
              !Primops.reverted{1}
            ) \/
            (
              !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
              res{2} = None /\
              Primops.reverted{1}
            )
          ).
              progress.
              exists (Primops.memory{1}) (Primops.reverted{1}) (p1_addr, p2_addr, dest_addr).
              progress.
              rewrite - H11. by progress.
              rewrite - H12. by progress.
              rewrite - H13. by progress.
              rewrite - H14. by progress.
              progress.
              conseq (_ :
            ={arg, glob PointAddIntoDest} /\
            arg{1} = (p1_addr, p2_addr, dest_addr) /\
              W256.of_int 128 <= p1_addr /\ W256.of_int 64 <= - p1_addr /\
              W256.of_int 128 <= p2_addr /\ W256.of_int 64 <= - p2_addr
            ==>  
            ={res, glob PointAddIntoDest}
          ).
              by progress.
              exact pointAddIntoDest_low_equiv_low'.
              conseq (_ :
              0 <= p1.`1 < FieldQ.p /\ 0 <= p2.`1 < FieldQ.p /\ 0 <= p1.`2 < FieldQ.p /\ 0 <= p2.`2 < FieldQ.p /\
              Primops.memory{1} = mem_0 /\
              PurePrimops.mload mem_0 p1_addr = W256.of_int p1.`1 /\
              PurePrimops.mload mem_0 (p1_addr + W256.of_int 32) = W256.of_int p1.`2 /\
              PurePrimops.mload mem_0 p2_addr = W256.of_int p2.`1 /\
              PurePrimops.mload mem_0 (p2_addr + W256.of_int 32) = W256.of_int p2.`2 /\
            arg{1} = (p1_addr, p2_addr, dest_addr) /\
            arg{2} = (p1.`1, p1.`2, p2.`1, p2.`2) /\
              !Primops.reverted{1}
      ==>
      (
        ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
        exists (x y : FieldQ.F),
        ecAdd_precompile (FieldQ.inF p1.`1) (FieldQ.inF p1.`2) (FieldQ.inF p2.`1) (FieldQ.inF p2.`2) = Some (x, y) /\
        res{2} = Some (FieldQ.asint x, FieldQ.asint y) /\
        Primops.memory{1} = pointAddIntoDest_memory_footprint mem_0 dest_addr p1 p2 (x, y) /\
        !Primops.reverted{1}
      ) \/
      (
        !ConcretePrimops.staticcall_ec_add_should_succeed (W256.of_int p1.`1, W256.of_int p1.`2) (W256.of_int p2.`1, W256.of_int p2.`2) /\
        res{2} = None /\
        Primops.reverted{1}
      )
    ).
        by progress.
        by progress.
        exact (pointAddIntoDest_low'_equiv_mid p1.`1 p2.`1 p1.`2 p2.`2 p1_addr p2_addr dest_addr mem_0).
  qed.

lemma pointAddIntoDest_mid_equiv_high_field:
equiv [
    PointAddIntoDest.mid ~ PointAddIntoDest.high_field:
      x1{1} = (F_to_int_point p1{2}).`1 /\
      y1{1} = (F_to_int_point p1{2}).`2 /\
      x2{1} = (F_to_int_point p2{2}).`1 /\
      y2{1} = (F_to_int_point p2{2}).`2 ==>
      (
        (res{1} = None /\ res{2} = None) \/
        (exists (ret_int: int*int, ret_f: FieldQ.F*FieldQ.F),
          res{1} = Some ret_int /\ res{2} = Some ret_f /\
          ret_int = F_to_int_point ret_f
        )
      )
    ].
    proof.
      proc.
      wp. skip.
      progress.
      do rewrite F_to_int_point_inzmod_1.
      do rewrite F_to_int_point_inzmod_2.
      case (ecAdd_precompile p1{2}.`1 p1{2}.`2 p2{2}.`1 p2{2}.`2).
      by progress.
    move=> p_add.
      progress.
      exists (F_to_int_point p_add); exists (p_add).
      by progress.
    qed.
          
lemma pointAddIntoDest_high_field_equiv_high:
equiv [
    PointAddIntoDest.high_field ~ PointAddIntoDest.high:
      aspoint_G1 p1{2} = p1{1} /\
      aspoint_G1 p2{2} = p2{1} ==>
      res{1} = Some (aspoint_G1 res{2})
    ].
    proof.
      proc.
      skip.
      progress.
      rewrite (ecAdd_def (aspoint_G1 p1{2}).`1 (aspoint_G1 p1{2}).`2 (aspoint_G1 p2{2}).`1 (aspoint_G1 p2{2}).`2 p1{2} p2{2}).
      smt (). smt (). reflexivity.
  qed.

lemma pointAddIntoDest_mid_equiv_high:
equiv [
    PointAddIntoDest.mid ~ PointAddIntoDest.high:
      x1{1} = (F_to_int_point (aspoint_G1 p1{2})).`1 /\
      y1{1} = (F_to_int_point (aspoint_G1 p1{2})).`2 /\    
      x2{1} = (F_to_int_point (aspoint_G1 p2{2})).`1 /\
      y2{1} = (F_to_int_point (aspoint_G1 p2{2})).`2 ==>
      res{1} = Some (F_to_int_point (aspoint_G1 res{2}))
    ].
    proof.
      transitivity PointAddIntoDest.high_field
    (
      x1{1} = (F_to_int_point p1{2}).`1 /\
      y1{1} = (F_to_int_point p1{2}).`2 /\
      x2{1} = (F_to_int_point p2{2}).`1 /\
      y2{1} = (F_to_int_point p2{2}).`2 ==>
      (
        (res{1} = None /\ res{2} = None) \/
        (exists (ret_int: int*int, ret_f: FieldQ.F*FieldQ.F),
          res{1} = Some ret_int /\ res{2} = Some ret_f /\
          ret_int = F_to_int_point ret_f
        )
      )
    )
    (
      aspoint_G1 p1{2} = p1{1} /\
      aspoint_G1 p2{2} = p2{1} ==>
      res{1} = Some (aspoint_G1 res{2})
    ).
        by progress; exists (aspoint_G1 p1{2}, aspoint_G1 p2{2}); progress.
        by progress; case H; progress.
        exact pointAddIntoDest_mid_equiv_high_field.
        exact pointAddIntoDest_high_field_equiv_high.
    qed.
      
