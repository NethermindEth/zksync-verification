pragma Goals:printall.

require import Array.
require import EllipticCurve.
require import Logic.
require import Memory.
require import PurePrimops.
require import Real.
require import UInt256.
require import Utils.
require import YulPrimops.
require import Verifier.

op p_int = 21888242871839275222246405745257275088696311157297823662689037894645226208583.
op p_uint256 = W256.of_int p_int.

(* Functional correctness *)

lemma usr_revertWithMessage_correctness :
    forall (size reason : uint256),
hoare [ Verifier_1261.usr_revertWithMessage :
      arg = (size, reason) ==>
    Primops.reverted = true
    ].
    proof.
      progress.
      proc.
      inline Primops.mload Primops.mstore Primops.revert.
      wp.
      skip.
      progress.
  qed.

  type Point = int * int.
  op NegatePoint (point: Point): Point = (point.`1, (-point.`2) %% p_int).
  op IsPointWellformed (point: Point): bool = 0 <= point.`1 /\ 0 <= point.`2 /\ point.`1 < p_int /\ point.`2 < p_int.
  op IsPointValid (point: Point): bool = !(point.`1 <> 0 /\ point.`2 = 0).

module PointNegate = {
  proc low(point: uint256) : unit = {
    var x, y;
    x <@ Primops.mload(point);
    y <@ Primops.mload(point + W256.of_int 32);
    if (y <> W256.zero) {
        Primops.mstore(point + W256.of_int 32, p_uint256 - y);
    }

    if (x <> W256.zero /\ y = W256.zero) {
      Primops.revert(W256.zero, W256.zero);
    }
  }

  proc mid(point_x: int, point_y: int) : int * int = {
    var ret_x, ret_y;
    ret_x <- point_x;
    ret_y <- (-point_y) %% p_int;

    if (point_x <> 0 /\ point_y = 0) {
      Primops.reverted <- true;
    }

    return (ret_x, ret_y);
  }

      proc high(point: Point): Point = {
    (* option instead of revert *)
    if (!IsPointValid point) {
      Primops.reverted <- true;
    }

    return (NegatePoint point);
  }
}.

lemma pointNegate_actual_matches_low: equiv [
    Verifier_1261.usr_pointNegate ~ PointNegate.low :
    Primops.memory{1} = Primops.memory{2} /\
      arg{1} = arg{2} /\
    !Primops.reverted{1} /\
    !Primops.reverted{2}
      ==>
        Primops.reverted{1} <=> Primops.reverted{2} /\
        (!Primops.reverted{1}) =>
        forall (idx: uint256),
        Primops.memory{1}.[idx] =
        Primops.memory{2}.[idx]
    ].
    proof.
      exists* Primops.memory{1}.
      elim*=>memory.
      exists* usr_point{1}.
      elim*=>point.
      proc.
      case (PurePrimops.mload memory (point+W256.of_int 32) = W256.zero). (* case y=0 *)
      rcondt{1} 6; first last.                                                   (* actual: take the no-writing branch *)
      rcondf{2} 3; first last.                                                   (* low: take the no-writing branch *)
      case (PurePrimops.mload memory point = W256.zero).                     (* case x=0 *)
      rcondf{1} 8; first last.                                                     (* actual: take the non-reverting branch *)
      rcondf{2} 3; first last.                                                     (* low: take the non-reverting branch *)
      sim.                                                                         (* simplify post to just equating memory *)
      inline Primops.mload.
      by sim.                                                                         (* prove memory is unchanged *)
      progress.                                                                    (* to prove: x and y are loaded correctly in the low spec *)
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).           (* load y *)
      call (ConcretePrimops.mload_spec memory point).                              (* load x *)
      skip.
      progress.
      rewrite H2 H1.
      by trivial.
      progress.                                                                    (* to prove: x is loaded correctly in actual *)
      wp.
      call (ConcretePrimops.mload_spec memory point).                              (* load x *)
      inline Primops.mload. wp. skip. by progress.                                    (* discharge the rest of the program *)
                                                                                 (* case x <> 0 *)
      rcondt{1} 8; first last.                                                     (* actual: take the reverting branch *)
      rcondt{2} 3; first last.                                                     (* low: take the reverting branch *)
      inline Verifier_1261.usr_revertWithMessage Primops.revert Primops.mstore Primops.mload. (* sim here breaks the proof *)
      wp. skip. by progress.
      progress.                                                                    (* to prove: x and y are loaded correctly in the low spec *)
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).           (* load y *)
      call (ConcretePrimops.mload_spec memory point).                              (* load x *)
      skip. by progress.
      progress.                                                                    (* to prove: x loaded correct in actual *)
      wp.
      call (ConcretePrimops.mload_spec memory point).
      inline Primops.mload. wp. skip. by progress.
      progress.                                                                  (* to prove: y loaded correctly in low *)
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      inline Primops.mload. wp. skip. by progress.
      progress.                                                                  (* to prove: y loaded correctly in actual *)
      wp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      wp. skip. by progress.
                                                                             (* case y<>0 *)
      rcondf{1} 6; first last.                                                 (* actual: take writing branch *)
      rcondf{2} 4; first last.                                                 (* low: skip reverting branch *)
      rcondt{2} 3; first last.                                                 (* low: take writing branch *)
      sim. inline Primops.mstore Primops.mload. wp. skip. by progress.         (* prove that neither revert and memory maps are modified equally *)
      progress.                                                                (* prove that y is loaded correct in low *)
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      inline Primops.mload. wp. skip. by progress.
      progress.                                                                (* prove that x and y are loaded correct in low and the writing branch is taken *)
      rcondt 3; first last.                                                    (* take the writing branch *)
      inline Primops.mstore. wp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point).
      skip. progress. rewrite H1. by trivial.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      inline Primops.mload. wp. skip. by progress.
      progress.                                                                (* prove y is loaded correctly in actual *)
      wp.
      call (ConcretePrimops.mload_spec memory (point + W256.of_int 32)).
      wp. skip. by progress.
  qed.

lemma pointNegate_low_matches_mid (memory: MemoryMap.mem) (point_address: uint256) (point_x_int point_y_int: int): equiv [
    PointNegate.low ~ PointNegate.mid :
      arg{2} = (point_x_int, point_y_int) /\
      arg{1} = point_address /\
      Primops.memory{1} = memory /\
      W256.to_uint(PurePrimops.mload memory point_address) = point_x_int /\
      W256.to_uint(PurePrimops.mload memory (point_address + W256.of_int 32)) = point_y_int /\
      !Primops.reverted{1} /\
      !Primops.reverted{2}
      ==>
        Primops.reverted{1} <=> Primops.reverted{2} /\ (
        (!Primops.reverted{1}) => (
          Primops.memory{1} = PurePrimops.mstore (PurePrimops.mstore memory point_address (W256.of_int res{2}.`1)) (point_address + W256.of_int 32) (W256.of_int res{2}.`2)
        ))
    ].
    proof.
      exists* Primops.memory{1}.
      elim*=> memory_pre.
      proc.
    case (point_y_int = 0).
      rcondf{1} 3. progress.
      call (ConcretePrimops.mload_spec memory (point_address + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point_address).
      skip. progress.
      apply zero_of_to_uint_zero. exact H1.
    case (point_x_int = 0).
      rcondf{1} 3. progress.
      call (ConcretePrimops.mload_spec memory (point_address + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point_address).
      skip. progress.
      by smt (zero_of_to_uint_zero).
      rcondf{2} 3. progress.
      wp. skip. progress.
      by smt (zero_of_to_uint_zero).
      wp.
      kill{1} 0 ! 2; first (inline Primops.mload; wp; skip; by progress).
      skip.
      by progress.
      (* case point_x_int <> 0 *)
      rcondt{1} 3. progress.
      call (ConcretePrimops.mload_spec memory (point_address + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point_address).
      skip. progress; by smt (@W256).
      rcondt{2} 3. progress.
      wp. skip. by progress.
      inline Primops.revert.
      kill{1} 0 ! 4. inline Primops.mload. wp. skip. by progress.
      wp. skip. by progress.
      (* case point_y_int <> 0 *)
      rcondt{1} 3. progress.
      call (ConcretePrimops.mload_spec memory (point_address + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point_address).
      skip. progress. by smt (@W256).
      rcondf{1} 4. progress.
      inline Primops.mstore. wp.
      call (ConcretePrimops.mload_spec memory (point_address + W256.of_int 32)).
      call (ConcretePrimops.mload_spec memory point_address).
      skip. progress. by smt (@W256).
      rcondf{2} 3. progress. wp. skip. progress. by smt (@W256).
      call{1} (ConcretePrimops.mstore_pspec memory_pre (point_address + W256.of_int 32) (p_uint256 - W256.of_int point_y_int)).
      call{1} (ConcretePrimops.mload_pspec memory_pre (point_address + W256.of_int 32)).
      call{1} (ConcretePrimops.mload_pspec memory_pre point_address).
      wp. skip. by progress.
    qed.

lemma pointNegate_mid_matches_high (point: Point):
  equiv [
    PointNegate.mid ~ PointNegate.high :
      arg{2} = (arg{1}.`1, arg{1}.`2) /\
      arg{2} = point /\
    IsPointWellformed point /\
    !Primops.reverted{1} /\
      !Primops.reverted{2}
      ==>
    (Primops.reverted{1} <=> Primops.reverted{2}) /\ (!Primops.reverted{1} => res{2} = (res{1}.`1, res{1}.`2))
  ].
  proof.
    proc.
    wp. skip. progress; by smt().
qed.

module PointMulIntoDest = {
  proc low(usr_point, usr_s, usr_dest) =
  {
    var _1, _5, _6,  _9, _10;
    _1 <@ Primops.mload(usr_point);
    Primops.mstore(W256.zero, _1);
    _5 <@ Primops.mload(usr_point + W256.of_int 32);
    Primops.mstore(W256.of_int 32, _5);
    Primops.mstore(W256.of_int 64, usr_s);
    _9 <@ Primops.gas();
    _10 <@ Primops.staticcall(_9, W256.of_int 7, W256.zero, W256.of_int 96, usr_dest, _6);
    if (bool_of_uint256 (PurePrimops.iszero(_10)))
    {
      Verifier_1261.usr_revertWithMessage(W256.of_int 30, W256.zero);
    }
  }
}.

lemma mstore_eq_of_eq (mem1 mem2 : MemoryMap.mem) (ind val : uint256) : mem1 = mem2 => PurePrimops.mstore mem1 ind val = PurePrimops.mstore mem2 ind val.
    proof.
      progress.
    qed.

lemma five_neq_seven : W256.of_int 7 <> W256.of_int 5.
proof.
  have Hle: W256.of_int 5 < W256.of_int 7 by smt(W256.ult_of_int).
  smt().  
qed.

lemma six_neq_seven : W256.of_int 7 <> W256.of_int 6.
proof.
  have Hle: W256.of_int 6 < W256.of_int 7 by smt(W256.ult_of_int).
  smt().
qed.

lemma one_neq_zero : W256.one <> W256.zero.
    proof.
  print W256.
(*  rewrite /W256.zero /W256.one.*)
  smt (@W256).  
qed.

import MemoryMap.
  
lemma usr_pointMulIntoDest_actual_matches_low (x y : uint256) : equiv [
    Verifier_1261.usr_pointMulIntoDest ~ PointMulIntoDest.low :
      ={Primops.memory} /\
      ={arg} /\
      ={Primops.reverted} /\
      !Primops.reverted{1}
      ==>
        (Primops.reverted{1} <=> Primops.reverted{2}) /\
        (!Primops.reverted{1}) =>
        forall (idx: uint256),
        Primops.memory{1}.[idx] =
        Primops.memory{2}.[idx]
    ].
    proof.
      proc.
      seq 1 1: (#pre /\ tmp53{1} = _1{2}).
      inline *. wp. skip. by progress.
      sp.
      seq 1 1: #pre.
      inline *. wp. skip. by progress.
      sp.
      seq 2 1: (#pre /\ _5{1} = _5{2}).
      inline *. wp. skip. by progress.
      seq 2 1: (#pre /\ _6{1} = (W256.of_int 64) /\ Primops.memory{1} = Primops.memory{2}).
      inline *. wp. skip. by progress.
      seq 1 1: (#pre /\ ={Primops.memory}).
      inline *. wp. skip. by progress.
      seq 4 1: (#pre /\ _7{1}=W256.of_int 96 /\ _8{1}=W256.of_int 7 /\ ={_9}).
      inline *. wp. skip. by progress.
      sp.
      inline Primops.staticcall.
      seq 1 1: (#pre).
      inline *. wp. skip. by progress.
      seq 1 1: (#pre /\ addr{1} = W256.of_int 7 /\ ={addr}).
      inline *. wp. skip. by progress.
      seq 1 1: (#pre /\ argOff{1} = _2{1} /\ ={argOff}).
      inline *. wp. skip. by progress.
      sp.
      
      seq 2 1: (#pre /\ )
    move => &1 &2.
      progress. smt().
      by progress.     
      
      (* exists* Primops.memory{1},  usr_point{1}, usr_s{2}.
      elim*. progress.
      pose mem_1 := PurePrimops.mstore memory_L W256.zero (PurePrimops.mload memory_L usr_point_L).
      have H_mem1 : load mem_1 (usr_point_L + W256.of_int 32) = load memory_L (usr_point_L + W256.of_int 32).
      rewrite /mem_1.
      apply load_store_diff.
      pose mem_2 := PurePrimops.mstore mem_1 (W256.of_int 32) (PurePrimops.mload memory_L (usr_point_L + W256.of_int 32)).
      pose mem_3 := PurePrimops.mstore mem_2 (W256.of_int 64) usr_s_R.
      seq 15 6: (Primops.memory{1} = mem_3 /\ Primops.memory{2} = mem_3).
      inline Primops.gas. wp.
      call {1} (ConcretePrimops.mstore_pspec mem_2 (W256.of_int 64) usr_s_R).
      call {2} (ConcretePrimops.mstore_pspec mem_2 (W256.of_int 64) usr_s_R).
      wp.
      call {1} (ConcretePrimops.mstore_pspec mem_1 (W256.of_int 32) (PurePrimops.mload memory_L (usr_point_L + W256.of_int 32))).
      call {2} (ConcretePrimops.mstore_pspec mem_1 (W256.of_int 32) (PurePrimops.mload memory_L (usr_point_L + W256.of_int 32))).
      wp.
      call {1} (ConcretePrimops.mload_pspec mem_1 (usr_point_L + W256.of_int 32)).
      call {2} (ConcretePrimops.mload_pspec mem_1 (usr_point_L + W256.of_int 32)).
      wp.      
      call {1} (ConcretePrimops.mstore_pspec memory_L (W256.zero) (PurePrimops.mload memory_L usr_point_L)).
      call {2} (ConcretePrimops.mstore_pspec memory_L (W256.zero) (PurePrimops.mload memory_L usr_point_L)).      wp.
      call {1} (ConcretePrimops.mload_pspec memory_L usr_point_L).
      call {2} (ConcretePrimops.mload_pspec memory_L usr_point_L).
      wp.
      skip. progress.
      rewrite /mem_1.
      apply MemoryMap.load_store_diff. smt (@W256).



    
      inline *; wp; skip.
    move=> &1 &2  H.
      simplify.
      rewrite five_neq_seven six_neq_seven PurePrimops.iszero_zeroE /bool_of_uint256 one_neq_zero.
      simplify.
      progress.
      smt().
      smt().
      smt().
      smt().
      simplify.
      progress.
      admit.
      smt().
      simplify.
      rewrite /odflt.
      
      

      smt(@W256 @Memory @EllipticCurve).
      rewrite - ecMul_def.
      simplify at H1.
    print ecMul_def.
      
      smt (@W256 @Memory.MemoryMap @EllipticCurve.ZModField @EllipticCurve ecMul_def).
        apply ecMul_def.
      
      smt().
      rewrite /bool_of_uint256.
      si
      progress.
      rewrite PurePrimops.iszero_zeroE.
      simplif
      progress.
      rewrite fi
      have Hseven_neq_five: W256.of_int 7 <> W256.of_int 5 by smt (five_neq_seven).
      rewrite Hseven_neq_five.
      simplify.
      progress.
      trivial.
      rcondf Hneq.
      progress.
      apply W256.ult_of_int_true.
    
     print W256.ule_of_in.
     have Hneq : (W256.of_int 7) <> (W256.of_int 5) by smt(W256.ule_of_int_true).      
   
      do! smt(@YulPrimops @Memory @Memory.MemoryMap).
      smt().
      exists* Primops.memory{1}.
      elim*=>memory.
      proc.
      exists* usr_point{1}.
      elim* => u_point.
      exists* usr_s{1}.
      elim* => u_s.
      exists* usr_dest{1}.
      elim* => u_dest.
      seq 2 1 :
      (u_dest = usr_dest{1} /\
        u_s = usr_s{1} /\
        u_point = usr_point{1} /\
        memory = Primops.memory{1} /\
        ={Primops.memory} /\
        (usr_point{1}, usr_s{1}, usr_dest{1}) =
        (usr_point{2}, usr_s{2}, usr_dest{2}) /\
        ={Primops.reverted} /\ !Primops.reverted{1} /\ _1{1} = _1{2} /\ _1{1} = PurePrimops.mload memory u_point).
      print YulPrimops.ConcretePrimops.mstore_spec.
      call YulPrimops.ConcretePrimops.mstore_spec.
          call YulVerifier.

        call Memory.MemoryMap.loadE.
      inline Primops.mload. wp. skip. progress.
      sp.
      seq 1 1 :
      (
        u_dest = usr_dest{1} /\
        u_s = usr_s{1} /\
        u_point = usr_point{1} /\
        (usr_point{1}, usr_s{1}, usr_dest{1}) = (usr_point{2}, usr_s{2}, usr_dest{2}) /\
        Primops.memory{1} = PurePrimops.mstore memory (W256.of_int 0) (PurePrimops.mload memory u_point) /\
        ={Primops.memory} /\
        ={Primops.reverted} /\
        !Primops.reverted{1}
      ).
      inline Primops.mstore. wp. skip. progress.
      sp.
      seq 2 1 :
      (
        _3{1} = W256.of_int 32 /\
        u_dest = usr_dest{1} /\
        u_s = usr_s{1} /\
        u_point = usr_point{1} /\
        (usr_point{1}, usr_s{1}, usr_dest{1}) = (usr_point{2}, usr_s{2}, usr_dest{2}) /\
        Primops.memory{1} = (PurePrimops.mstore memory W256.zero ((PurePrimops.mload memory u_point))) /\
        ={Primops.memory} /\ ={Primops.reverted} /\ !Primops.reverted{1} /\
        _5{1} = _5{2} /\ _5{1} = PurePrimops.mload Primops.memory{1} (usr_point{1} + W256.of_int 32)
      ).
      inline Primops.mload. wp. skip. move=> &1 &2 H. progress. smt (). smt (). smt (). smt (). admit. admit. admit. smt (). smt (). smt (). smt (). smt (). smt ().
      seq 1 1 :
      (
        u_dest = usr_dest{1} /\
        u_s = usr_s{1} /\
        u_point = usr_point{1} /\
        (usr_point{1}, usr_s{1}, usr_dest{1}) =
        (usr_point{2}, usr_s{2}, usr_dest{2}) /\
          Primops.memory{1} =
        (PurePrimops.mstore (PurePrimops.mstore memory W256.zero (PurePrimops.mload memory u_point)) (W256.of_int 32) (PurePrimops.mload Primops.memory{1} (usr_point{1} + (W256.of_int 32)))) /\
        ={Primops.memory} /\
        ={Primops.reverted} /\ !Primops.reverted{1}
      ).
      inline Primops.mstore. wp. skip. move=> &1 &2 H. simplify.
      progress. smt (). smt (). smt (). smt (). admit. admit.
      have H1 : _3{1} = W256.of_int 32. smt ().
      have H2 : Primops.memory{1} = (PurePrimops.mstore memory W256.zero (PurePrimops.mload memory u_point)). smt ().
          rewrite H1 H2.
          simplify.
          print Memory.
          rewrite Memory.MemoryMap.storeE.
          inline mstore.
          apply mstore_eq_of_eq .
      
      have H1 : Primops.memory{1} = Primops.memory{2}. smt ().
          have H2 : usr_point{2} = usr_point{1}. smt ().
          rewrite H2.
          have H3 : 
          rewrite H1.
      
          Primops.mstore Primops.gas Verifier_1261.usr_revertWithMessage Primops.staticcall bool_of_uint256.
    inline PurePrimops.iszero.
      sim.
      wp.
      sp.
      sim.
      progress.
      simplify.
    print ConcretePrimops.mload_spec.
      call (ConcretePrimops.mload_spec memory u_pt). *)
