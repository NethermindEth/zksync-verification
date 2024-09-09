pragma Goals:printall.
prover timeout=10.

require import AllCore.
require import List.
require import Array.
require import Int.
require import IntDiv.
require import Logic.
require import PurePrimops.
require import Utils.
require export EllipticCurve.
require import Field.
require export Memory.
require export UInt256.

import MemoryMap.

module Primops = {
  var memory : mem
  var ret_data : mem
  var reverted : bool

  proc mload(idx : uint256) : uint256 = {
    return (PurePrimops.mload memory idx);
  }

  proc mstore(idx : uint256, val : uint256): unit = {
    memory <- PurePrimops.mstore memory idx val;
  }

  proc mstore8(idx : uint256, val : uint256) : unit = {
    memory <- PurePrimops.mstore8 memory idx val;
  }

  proc evm_return(retOff : uint256, retSize : uint256) : unit = {
      ret_data <- Map.offun (fun (i: uint256) =>
      if retSize <= i then witness
      else memory.[retOff + i]);
      return ();
  }

  proc pop(x : uint256) : unit = {
    return ();
  }

  proc gas() : uint256 = {
    return W256.of_int 42;
  }

  proc callvalue() = {
      return PurePrimops.callvalue;
  }

  proc keccak256(off : uint256, size : uint256) : uint256 = {
      var input : uint8 array;
      input <- Array.offun (fun (i: int) => memory.[off + (W256.of_int i)]) (W256.to_uint size);
      return PurePrimops.keccak256_f input;
  }

  proc staticcall(gas : uint256, addr : uint256, argOff : uint256, argSize : uint256, retOff : uint256, retSize : uint256) : uint256 = {
      var succ;
      var bsize, esize, msize : uint256;
      var base, exp, mod;
      var x1, y1, x2, y2, x3, y3, x2_1, x2_2, y2_1, y2_2, x4_1, x4_2, y4_1, y4_2;
      var s;
      var sv;
      var x1_F, y1_F, x2_F, y2_F, x3_F, y3_F, x2_1_F, x2_2_F, y2_1_F, y2_2_F, x4_1_F, x4_2_F, y4_1_F, y4_2_F;
      var result;
      var result_unwrap;
      var result_b;
      var result_b_unwrap;
      succ <- W256.zero;
      if (addr = W256.of_int 5) {
        bsize <@ mload(argOff);
        esize <@ mload(argOff + W256.of_int 32);
        msize <@ mload(argOff + W256.of_int 64);
        if (bsize = (W256.of_int 32) /\ esize = (W256.of_int 32) /\ msize = (W256.of_int 32) /\ retSize = (W256.of_int 32) /\ argSize = (W256.of_int 192)) {
          base <@ mload(argOff + W256.of_int 96);
          exp  <@ mload(argOff + W256.of_int 128);
          mod  <@ mload(argOff + W256.of_int 160);
          mstore(retOff, W256.of_int (((W256.to_uint base) ^ (W256.to_uint exp)) %% (W256.to_uint mod)));
          succ <- W256.one;
        } else {
          succ <- W256.zero;
        }
      } else {
        if (addr = W256.of_int 6) {
          if (retSize = (W256.of_int 64) /\ argSize = (W256.of_int 128)) {
            x1 <@ mload(argOff);
            y1 <@ mload(argOff + W256.of_int 32);
            x2 <@ mload(argOff + W256.of_int 64);
            y2 <@ mload(argOff + W256.of_int 96);
            x1_F <- FieldQ.inF (W256.to_uint x1);
            y1_F <- FieldQ.inF (W256.to_uint y1);
            x2_F <- FieldQ.inF (W256.to_uint x2);
            y2_F <- FieldQ.inF (W256.to_uint y2);
            if (x1 <> x1 %% W256.of_int FieldQ.p \/ y1 <> y1 %% W256.of_int FieldQ.p \/ x2 <> x2 %% W256.of_int FieldQ.p \/ y2 <> y2 %% W256.of_int FieldQ.p) {
              succ <- W256.zero;
            } else {
              if (!(on_curve (x1_F, y1_F)) \/ !(on_curve ((x2_F, y2_F)))) {
                succ <- W256.zero;
              } else {
                result <- ecAdd_precompile x1_F y1_F x2_F y2_F;
                if (is_none result) {
                  succ <- W256.zero;
                } else {
                    result_unwrap <- odflt (FieldQ.zero, FieldQ.zero) result;
                    mstore(retOff, W256.of_int (FieldQ.asint (fst result_unwrap)));
                    mstore(retOff + W256.of_int 32, W256.of_int (FieldQ.asint (snd (result_unwrap))));
                    succ <- W256.one;
                }                
              }
            }
          } else {
            succ <- W256.zero;
          } 
        } else {
          if (addr = W256.of_int 7) {
            if (retSize = (W256.of_int 64) /\ argSize = (W256.of_int 96)) {
              x1 <@ mload(argOff);
              y1 <@ mload(argOff + W256.of_int 32);
              s <@ mload(argOff + W256.of_int 64);
              x1_F <- FieldQ.inF (W256.to_uint x1);
              y1_F <- FieldQ.inF (W256.to_uint y1);
              sv <- W256.to_uint s;
              if (x1 <> x1 %% W256.of_int FieldQ.p \/ y1 <> y1 %% W256.of_int FieldQ.p) {
                succ <- W256.zero;
              } else {
                if (!(on_curve (x1_F, y1_F))) {
                  succ <- W256.zero;
                } else {
                  result <- ecMul_precompile x1_F y1_F sv;
                  if (is_none result) {
                    succ <- W256.zero;
                  } else {
                      result_unwrap <- odflt (FieldQ.zero, FieldQ.zero) result;
                      mstore(retOff, W256.of_int (FieldQ.asint (fst result_unwrap)));
                      mstore(retOff + W256.of_int 32, W256.of_int (FieldQ.asint (snd (result_unwrap))));
                      succ <- W256.one;
                  }                
                }
              }
            }
          } else {
            if (addr = W256.of_int 8) {
              if (retSize = (W256.of_int 32) /\ argSize = (W256.of_int 384)) {
                  x1 <@ mload(argOff);
                  y1 <@ mload(argOff + W256.of_int 32);
                  x2_1 <@ mload(argOff + W256.of_int 64);
                  x2_2 <@ mload(argOff + W256.of_int 96);
                  y2_1 <@ mload(argOff + W256.of_int 128);
                  y2_2 <@ mload(argOff + W256.of_int 160);
                  x3 <@ mload(argOff + W256.of_int 192);
                  y3 <@ mload(argOff + W256.of_int 224);
                  x4_1 <@ mload(argOff + W256.of_int 256);
                  x4_2 <@ mload(argOff + W256.of_int 288);
                  y4_1 <@ mload(argOff + W256.of_int 320);
                  y4_2 <@ mload(argOff + W256.of_int 352);
                  x1_F <- FieldQ.inF (W256.to_uint x1);
                  y1_F <- FieldQ.inF (W256.to_uint y1);
                  x2_1_F <- FieldQ.inF (W256.to_uint x2_1);
                  x2_2_F <- FieldQ.inF (W256.to_uint x2_2);
                  y2_1_F <- FieldQ.inF (W256.to_uint y2_1);
                  y2_2_F <- FieldQ.inF (W256.to_uint y2_2);
                  x3_F <- FieldQ.inF (W256.to_uint x3);
                  y3_F <- FieldQ.inF (W256.to_uint y3);
                  x4_1_F <- FieldQ.inF (W256.to_uint x4_1);
                  x4_2_F <- FieldQ.inF (W256.to_uint x4_2);
                  y4_1_F <- FieldQ.inF (W256.to_uint y4_1);
                  y4_2_F <- FieldQ.inF (W256.to_uint y4_2);
                  if (x1 <> x1 %% W256.of_int FieldQ.p \/ y1 <> y1 %% W256.of_int FieldQ.p
                      \/ x2_1 <> x2_1 %% W256.of_int FieldQ.p \/ x2_2 <> x2_2 %% W256.of_int FieldQ.p
                      \/ y2_1 <> y2_1 %% W256.of_int FieldQ.p \/ y2_2 <> y2_2 %% W256.of_int FieldQ.p
                      \/ x3 <> x3 %% W256.of_int FieldQ.p \/ y3 <> y3 %% W256.of_int FieldQ.p
                      \/ x4_1 <> x4_1 %% W256.of_int FieldQ.p \/ x4_2 <> x4_2 %% W256.of_int FieldQ.p
                      \/ y4_1 <> y4_1 %% W256.of_int FieldQ.p \/ y4_2 <> y4_2 %% W256.of_int FieldQ.p) {
                      succ <- W256.zero;
                  } else {
                      if (!(on_curve (x1_F, y1_F)) \/ !(on_curve (x3_F, y3_F))
                          \/ !(on_curve_G2 ((x2_1_F, x2_2_F), (y2_1_F, y2_2_F)))
                          \/ !(on_curve_G2 ((x4_1_F, x4_2_F), (y4_1_F, y4_2_F)))) {
                        succ <- W256.zero;
                      } else {
                        result_b <- ecPairing_precompile ((x1_F, y1_F), ((x2_1_F, x2_2_F), (y2_1_F, y2_2_F))) ((x3_F, y3_F), ((x4_1_F, x4_2_F), (y4_1_F, y4_2_F)));
                        if (is_none result_b) {
                          succ <- W256.zero;
                        } else {
                          result_b_unwrap <- odflt false result_b;
                          mstore(retOff, UInt256.uint256_of_bool result_b_unwrap);
                          succ <- W256.one;
                        }
                      }
                 }
              } else {
                  succ <- W256.zero;
              }
            } else {
                succ <- W256.zero;
            }
          }
        }
      }
    return succ;
  }

  proc revert(x : uint256, y : uint256) : unit = {
    reverted <- true;
  }

  proc calldataload(i : uint256) : uint256 = {
    return load PurePrimops.calldata i;
  }

  proc calldatasize() = {
    return PurePrimops.calldatasize;
  }
}.

theory ConcretePrimops.

lemma mload_pspec (memory: mem) (idx: uint256):
phoare [ Primops.mload :
    arg = idx /\
    Primops.memory = memory ==>
      res = PurePrimops.mload memory idx /\
      Primops.memory = memory
    ] = 1%r.
    proof.
      progress.
      proc.
      wp.
      skip.
      by progress.
  qed.

lemma mload_pspec_revert :
phoare [ Primops.mload : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; skip; by auto. qed.

lemma mload_spec (memory: mem) (idx: uint256):
hoare [ Primops.mload :
    arg = idx /\
    Primops.memory = memory ==>
      res = PurePrimops.mload memory idx /\
      Primops.memory = memory
    ].
    proof.
      progress.
      proc.
      wp.
      skip.
      by progress.
  qed.

lemma mload_spec_revert:
hoare [ Primops.mload: Primops.reverted ==> Primops.reverted ].
    proof. proc. skip. by auto. qed.

lemma mstore_pspec:
    forall (memory: mem) (idx': uint256) (val': uint256),
phoare [ Primops.mstore :
    arg = (idx', val') /\
    Primops.memory = memory  ==>
      Primops.memory = PurePrimops.mstore memory idx' val'
    ] = 1%r.
    proof.
      progress.
      proc.
      wp.
      skip.
      by progress.
    qed.

lemma mstore_pspec_revert :
phoare [ Primops.mstore : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; wp; skip; by auto. qed.
    
lemma mstore_spec:
    forall (memory: mem) (idx': uint256) (val': uint256),
hoare [ Primops.mstore :
    arg = (idx', val') /\
    Primops.memory = memory ==>
      Primops.memory = PurePrimops.mstore memory idx' val'
    ].
    proof.
      progress.
      proc.
      wp.
      skip.
      by progress.
  qed.

lemma mstore_spec_revert:
hoare [ Primops.mstore: Primops.reverted ==> Primops.reverted ].
    proof. proc. wp. skip. by auto. qed.
  
lemma mstore8_pspec:
    forall (memory: mem) (idx': uint256) (val': uint256),
phoare [ Primops.mstore8 :
    arg = (idx', val') /\
    Primops.memory = memory  ==>
      Primops.memory = PurePrimops.mstore8 memory idx' val'
    ] = 1%r.
    proof.
      progress.
      proc.
      wp.
      skip.
      by progress.
    qed.

lemma mstore8_pspec_revert :
phoare [ Primops.mstore8 : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; wp; skip; by auto. qed.
    
lemma mstore8_spec:
    forall (memory: mem) (idx': uint256) (val': uint256),
hoare [ Primops.mstore8 :
    arg = (idx', val') /\
    Primops.memory = memory ==>
      Primops.memory = PurePrimops.mstore8 memory idx' val'
    ].
    proof.
      progress.
      proc.
      wp.
      skip.
      by progress.
  qed.
  
lemma keccak256_pspec (off size: uint256):
    phoare [ Primops.keccak256 :
      arg = (off, size) ==>
      res = PurePrimops.keccak256_f(Array.offun (fun (i: int) => Primops.memory.[off + (W256.of_int i)]) (W256.to_uint size))
    ] = 1%r.
    proof.
      proc.
      wp.
      skip.
      by progress.
  qed.

lemma keccak256_pspec_revert :
phoare [ Primops.keccak256 : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; wp; skip; by auto. qed.
  
lemma calldataload_pspec (idx: uint256):
    phoare [Primops.calldataload:
      arg = idx ==>
      res = load PurePrimops.calldata idx
    ] = 1%r.
    proof.
      proc.
      wp.
      skip.
      by progress.
  qed.

lemma calldataload_pspec_revert :
phoare [ Primops.calldataload : Primops.reverted ==> Primops.reverted ] = 1%r.
proof. proc; wp; skip; by auto. qed.
  
lemma staticcall_modexp_spec (memory: mem) (a b c gas argOff retOff: uint256):
    hoare [ Primops.staticcall:
      arg = (gas, W256.of_int 5, argOff, W256.of_int 192, retOff, W256.of_int 32) /\
      Primops.memory = memory /\
      PurePrimops.mload memory argOff = W256.of_int 32 /\
      PurePrimops.mload memory (argOff + (W256.of_int 32)) = W256.of_int 32 /\
      PurePrimops.mload memory (argOff + (W256.of_int 64)) = W256.of_int 32 /\
      PurePrimops.mload memory (argOff + (W256.of_int 96)) = a /\
      PurePrimops.mload memory (argOff + (W256.of_int 128)) = b /\
      PurePrimops.mload memory (argOff + (W256.of_int 160)) = c ==>
    Primops.memory = PurePrimops.mstore memory retOff (PurePrimops.modexp a b c) /\
      res = W256.one
    ].
    proof.
      proc.
      sp.
      rcondt 1. skip. by progress.
      seq 3 : (#pre /\ bsize = W256.of_int 32 /\ esize = W256.of_int 32 /\ msize = W256.of_int 32).
      inline Primops.mload. wp. skip. by progress.
      rcondt 1. skip. by progress.
      seq 3 : (#pre /\ base = a /\ exp = b /\ mod = c).
      inline Primops.mload. wp. skip. by progress.
      wp.
      call (ConcretePrimops.mstore_spec memory retOff (PurePrimops.modexp a b c)).
      skip.
      progress.
      rewrite PurePrimops.modexpE.
      reflexivity.
  qed.
  
lemma staticcall_modexp_pspec (memory: mem) (a b c gas argOff retOff: uint256):
    phoare [ Primops.staticcall:
      arg = (gas, W256.of_int 5, argOff, W256.of_int 192, retOff, W256.of_int 32) /\
      Primops.memory = memory /\
      PurePrimops.mload memory argOff = W256.of_int 32 /\
      PurePrimops.mload memory (argOff + (W256.of_int 32)) = W256.of_int 32 /\
      PurePrimops.mload memory (argOff + (W256.of_int 64)) = W256.of_int 32 /\
      PurePrimops.mload memory (argOff + (W256.of_int 96)) = a /\
      PurePrimops.mload memory (argOff + (W256.of_int 128)) = b /\
      PurePrimops.mload memory (argOff + (W256.of_int 160)) = c ==>
    Primops.memory = PurePrimops.mstore memory retOff (PurePrimops.modexp a b c) /\
      res = W256.one
    ] = 1%r.
    proof.
      proc.
      sp.
      rcondt 1. skip. by progress.
      rcondt 4.
      inline Primops.mload. wp. skip. by progress.
      wp.
      call (ConcretePrimops.mstore_pspec memory retOff (PurePrimops.modexp a b c)).
      inline Primops.mload. wp. skip.
      progress.
      rewrite PurePrimops.modexpE.
      reflexivity.
  qed.

pred point_wellformed (pnt: uint256*uint256) =
    pnt.`1 = pnt.`1 %% W256.of_int FieldQ.p /\
    pnt.`2 = pnt.`2 %% W256.of_int FieldQ.p.
pred point_oncurve (pnt: uint256*uint256) =
    on_curve ((FieldQ.inF(to_uint pnt.`1)), (FieldQ.inF(to_uint pnt.`2))).
pred staticcall_ec_add_should_succeed (p1 p2: uint256 * uint256) =
    point_wellformed p1 /\
    point_wellformed p2 /\
    point_oncurve p1 /\
    point_oncurve p2 /\
    is_some (ecAdd_precompile (FieldQ.inF(to_uint p1.`1)) (FieldQ.inF(to_uint p1.`2)) (FieldQ.inF(to_uint p2.`1)) (FieldQ.inF(to_uint p2.`2))).

op ecAdd_precompile_unsafe_cast (p1 p2: uint256 * uint256): (uint256*uint256) =
  let x1 = FieldQ.inF(to_uint p1.`1) in
  let y1 = FieldQ.inF(to_uint p1.`2) in
  let x2 = FieldQ.inF(to_uint p2.`1) in
  let y2 = FieldQ.inF(to_uint p2.`2) in
  let ret = ecAdd_precompile x1 y1 x2 y2 in
  let ret_unwrapped = odflt (FieldQ.zero, FieldQ.zero) ret in
  let x_ret = W256.of_int (FieldQ.asint ret_unwrapped.`1) in
  let y_ret = W256.of_int (FieldQ.asint ret_unwrapped.`2) in
  (x_ret,y_ret).

lemma staticcall_ec_add_pspec (memory: mem) (p1 p2: uint256 * uint256) (argOff retOff: uint256):
    phoare [ Primops.staticcall :
      arg = (gas, W256.of_int 6, argOff, W256.of_int 128, retOff, W256.of_int 64) /\
      Primops.memory = memory /\
      p1.`1 = PurePrimops.mload memory argOff /\
      p1.`2 = PurePrimops.mload memory (argOff + W256.of_int 32) /\
      p2.`1 = PurePrimops.mload memory (argOff + W256.of_int 64) /\
      p2.`2 = PurePrimops.mload memory (argOff + W256.of_int 96)
      ==>
      ((staticcall_ec_add_should_succeed p1 p2) => (
        res = W256.one /\
        Primops.memory = PurePrimops.mstore
          (PurePrimops.mstore
            memory
            retOff
            (ecAdd_precompile_unsafe_cast p1 p2).`1
          )
          (retOff + W256.of_int 32)
          (ecAdd_precompile_unsafe_cast p1 p2).`2
      )) /\
      ((!staticcall_ec_add_should_succeed p1 p2) => res = W256.zero /\ Primops.memory = memory)
    ] = 1%r.
    proof.
      proc.
      sp.
      inline *.
      rcondf 1. skip. progress. by smt(@W256).
      rcondt 1. skip. by progress.
      case (staticcall_ec_add_should_succeed p1 p2).
      rewrite /staticcall_ec_add_should_succeed /point_oncurve /point_wellformed.
      rcondt 1. skip. by progress.
      rcondf 13. wp. skip. progress. by smt().
      rcondf 13. wp. skip. progress. by smt ().
      rcondf 14. wp. skip. progress. by smt (is_none_iff_not_is_some).
      wp. skip. progress.
      rewrite /ecAdd_precompile_unsafe_cast.
      simplify.
      smt ().
      smt (). smt ().
    case (!point_wellformed p1 \/ !point_wellformed p2).
      rcondt 1. skip. by progress.
      rcondt 13. wp. skip. progress. by smt ().
      wp. skip. by progress.
      rcondt 1. skip. by progress.
      rcondf 13. wp. skip. progress. by smt ().
    case (!point_oncurve p1 \/ !point_oncurve p2).
      rcondt 13. wp. skip. progress. by smt ().
      wp. skip. by progress.
      rcondf 13. wp. skip. progress. by smt ().
      rcondt 14. wp. skip. progress. by smt ().
      wp. skip. by progress.
    qed.

lemma staticcall_pspec_revert :
phoare [ Primops.staticcall : Primops.reverted ==> Primops.reverted ] = 1%r.
    proof. proc; inline*; wp; by progress. qed.

lemma staticcall_spec_revert:
hoare [ Primops.staticcall : Primops.reverted ==> Primops.reverted ].
    proof. proc. inline*. wp. by progress. qed.

lemma ecAdd_precomp_is_some_of_should_succeed (p1 p2 : uint256 * uint256) :
    staticcall_ec_add_should_succeed p1 p2 =>
    is_some
    (ecAdd_precompile
      (FieldQ.inF (W256.to_uint p1.`1))
      (FieldQ.inF (W256.to_uint p1.`2))
      (FieldQ.inF (W256.to_uint p2.`1))
      (FieldQ.inF (W256.to_uint p2.`2))
    ). progress. smt (). qed.

lemma ecAdd_precomp_is_none_of_should_not_succeed (p1 p2 : uint256 * uint256) :
    ((W256.to_uint p1.`1) < FieldQ.p /\ W256.to_uint p1.`2 < FieldQ.p /\
      (W256.to_uint p2.`1) < FieldQ.p /\ W256.to_uint p2.`2 < FieldQ.p /\ 
    ! (staticcall_ec_add_should_succeed p1 p2)) =>
    is_none
      (ecAdd_precompile
        ((FieldQ.inF (W256.to_uint p1.`1)))
        ((FieldQ.inF (W256.to_uint p1.`2)))
        ((FieldQ.inF (W256.to_uint p2.`1)))
        ((FieldQ.inF (W256.to_uint p2.`2)))
      ).
          progress.
          rewrite /staticcall_ec_add_should_succeed in H3.
          have H_options: (
        (!point_wellformed p1) \/
        (!point_wellformed p2) \/
        (!point_oncurve p1) \/
        (!point_oncurve p2) \/
        (!is_some (ecAdd_precompile (FieldQ.inF(W256.to_uint p1.`1)) (FieldQ.inF(W256.to_uint p1.`2)) (FieldQ.inF(W256.to_uint p2.`1)) (FieldQ.inF(W256.to_uint p2.`2))))
      ) by smt ().
          case H_options.
          rewrite /point_wellformed. progress.
          have H_p1: (
        (p1.`1 = p1.`1 %% W256.of_int FieldQ.p) /\
        (p1.`2 = p1.`2 %% W256.of_int FieldQ.p)
      ).
          split.
          rewrite uint256_mod_eq_of_lt. rewrite uint256_lt_of_lt. rewrite W256.of_uintK. rewrite pmod_small. rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. by progress.
          assumption.
          reflexivity.
          rewrite uint256_mod_eq_of_lt. rewrite uint256_lt_of_lt. rewrite W256.of_uintK. rewrite pmod_small. rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. by progress.
          assumption.
          reflexivity.
          by progress.
      move=> H_options.
      case H_options.
          rewrite /point_wellformed. progress.
          have H_p2: (
        (p2.`1 = p2.`1 %% W256.of_int FieldQ.p) /\
        (p2.`2 = p2.`2 %% W256.of_int FieldQ.p)
      ).
          split.
          rewrite uint256_mod_eq_of_lt. rewrite uint256_lt_of_lt. rewrite W256.of_uintK. rewrite pmod_small. rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. by progress.
          assumption.
          reflexivity.
          rewrite uint256_mod_eq_of_lt. rewrite uint256_lt_of_lt. rewrite W256.of_uintK. rewrite pmod_small. rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. by progress.
          assumption.
          reflexivity.
          by progress.
      move=> H_options.
          case H_options.
          rewrite /point_oncurve. progress.
          apply is_none_of_eq_none.
          apply ecAdd_fail.
          left. assumption.
      move=> H_options.
          case H_options.
          rewrite /point_oncurve. progress.
          apply is_none_of_eq_none.
          apply ecAdd_fail.
          right. assumption.
      move=> H_not_is_some.
      exact is_none_iff_not_is_some.
    qed.
    
pred staticcall_ec_mul_should_succeed (p : uint256 * uint256) (s : uint256) =
    point_wellformed p /\
    point_oncurve p /\
    is_some (ecMul_precompile (FieldQ.inF(to_uint p.`1)) (FieldQ.inF(to_uint p.`2)) (to_uint s)).

op ecMul_precompile_unsafe_cast (p : uint256 * uint256) (s : uint256) : (uint256*uint256) =
  let x = FieldQ.inF(to_uint p.`1) in
  let y = FieldQ.inF(to_uint p.`2) in
  let ret = ecMul_precompile x y (W256.to_uint s) in
  let ret_unwrapped = odflt (FieldQ.zero, FieldQ.zero) ret in
  let x_ret = W256.of_int (FieldQ.asint ret_unwrapped.`1) in
  let y_ret = W256.of_int (FieldQ.asint ret_unwrapped.`2) in
  (x_ret,y_ret).

lemma ecMul_precomp_is_some_of_should_succeed (p : uint256 * uint256) (s : uint256) :
    staticcall_ec_mul_should_succeed p s =>
    is_some
      (ecMul_precompile ((FieldQ.inF (W256.to_uint p.`1)))
         ((FieldQ.inF (to_uint p.`2)))
         (to_uint s)). progress. smt (). qed.

lemma ecMul_precomp_is_none_of_should_not_succeed (p1 : uint256 * uint256) (s : uint256) :
    ((W256.to_uint p1.`1) < FieldQ.p /\ W256.to_uint p1.`2 < FieldQ.p /\ 
    ! (staticcall_ec_mul_should_succeed p1 s)) =>
    is_none
      (ecMul_precompile ((FieldQ.inF (W256.to_uint p1.`1)))
         ((FieldQ.inF (to_uint p1.`2)))
         (to_uint s)). progress.
           have H2 :
       (
         ! point_wellformed p1 \/
         ! point_oncurve p1 \/
         ! is_some (ecMul_precompile (FieldQ.inF(to_uint p1.`1)) (FieldQ.inF(to_uint p1.`2)) (to_uint s))
       ). smt ().
           case H2.
           progress. rewrite /point_wellformed in H2.
           have H3 : (p1.`1 <> p1.`1 %% (of_int FieldQ.p)%W256 \/ p1.`2 <> p1.`2 %% (of_int FieldQ.p)%W256). smt ().
           rewrite uint256_mod_eq_of_lt in H3. apply uint256_lt_of_lt. rewrite to_uint_small. progress.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
           assumption.
           rewrite uint256_mod_eq_of_lt in H3. apply uint256_lt_of_lt. rewrite to_uint_small. progress.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
           rewrite -Constants.q_eq_fieldq_p /Constants.Q. by progress.
           assumption.
           smt ().
       move=> [J | J'].
           rewrite /point_oncurve in J.
           apply is_none_of_eq_none.
           apply ecMul_fail. exact J.
           rewrite is_none_iff_not_is_some.
           exact J'.
     qed.
       
     
lemma staticcall_ec_mul_pspec (memory: mem) (p : uint256 * uint256) (s : uint256) (argOff retOff: uint256):
    phoare [ Primops.staticcall :
      arg = (gas, W256.of_int 7, argOff, W256.of_int 96, retOff, W256.of_int 64) /\
      Primops.memory = memory /\
      p.`1 = PurePrimops.mload memory argOff /\
      p.`2 = PurePrimops.mload memory (argOff + W256.of_int 32) /\
      s = PurePrimops.mload memory (argOff + W256.of_int 64)
      ==>
      ((staticcall_ec_mul_should_succeed p s) => (
        res = W256.one /\
        Primops.memory = PurePrimops.mstore
          (PurePrimops.mstore
            memory
            retOff
            (ecMul_precompile_unsafe_cast p s).`1
          )
          (retOff + W256.of_int 32)
          (ecMul_precompile_unsafe_cast p s).`2
      )) /\
      ((!staticcall_ec_mul_should_succeed p s) => res = W256.zero /\ Primops.memory = memory)
    ] = 1%r.
    proof.
      proc.

      inline *. wp. skip. progress.
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). 


      have CONT := ecMul_precomp_is_some_of_should_succeed _ _ H6. smt ().
      have CONT := ecMul_precomp_is_some_of_should_succeed _ _ H6. smt ().
      have CONT := ecMul_precomp_is_some_of_should_succeed _ _ H6. smt ().

      rewrite neg_none_eq_some in H5. smt ().
      rewrite neg_none_eq_some in H5. smt ().
  qed.

  pred point_G2_wellformed (pnt: ((uint256*uint256) * (uint256*uint256))) =
    pnt.`1.`1 = pnt.`1.`1 %% W256.of_int FieldQ.p /\
    pnt.`1.`2 = pnt.`1.`2 %% W256.of_int FieldQ.p /\
    pnt.`2.`1 = pnt.`2.`1 %% W256.of_int FieldQ.p /\
    pnt.`2.`2 = pnt.`2.`2 %% W256.of_int FieldQ.p.
  pred point_oncurve_G2 (pnt: (uint256*uint256) * (uint256 * uint256)) =
    on_curve_G2 ((FieldQ.inF(to_uint pnt.`1.`1), FieldQ.inF (to_uint pnt.`1.`2)), (FieldQ.inF(to_uint pnt.`2.`1), (FieldQ.inF (to_uint pnt.`2.`2)))).

  op ecPairing_precompile_unsafe_cast (p1 p2 : uint256 * uint256) (q1 q2 : (uint256*uint256) * (uint256*uint256)) : uint256 =
  let x1_F = FieldQ.inF (W256.to_uint p1.`1) in
  let y1_F = FieldQ.inF (W256.to_uint p1.`2) in
  let x2_1_F = FieldQ.inF (W256.to_uint q1.`1.`1) in
  let x2_2_F = FieldQ.inF (W256.to_uint q1.`1.`2) in
  let y2_1_F = FieldQ.inF (W256.to_uint q1.`2.`1) in
  let y2_2_F = FieldQ.inF (W256.to_uint q1.`2.`2) in
  let x3_F = FieldQ.inF (W256.to_uint p2.`1) in
  let y3_F = FieldQ.inF (W256.to_uint p2.`2) in
  let x4_1_F = FieldQ.inF (W256.to_uint q2.`1.`1) in
  let x4_2_F = FieldQ.inF (W256.to_uint q2.`1.`2) in
  let y4_1_F = FieldQ.inF (W256.to_uint q2.`2.`1) in
  let y4_2_F = FieldQ.inF (W256.to_uint q2.`2.`2) in
  let ret = ecPairing_precompile ((x1_F, y1_F), ((x2_1_F, x2_2_F), (y2_1_F, y2_2_F))) ((x3_F, y3_F), ((x4_1_F, x4_2_F), (y4_1_F, y4_2_F))) in
  let ret_unwrapped = odflt false ret in
  UInt256.uint256_of_bool ret_unwrapped.
  
  pred staticcall_ec_pairing_should_succeed (p1 p2 : uint256 * uint256) (q1 q2 : (uint256*uint256) * (uint256*uint256)) =
    point_wellformed p1 /\
    point_wellformed p2 /\
    point_G2_wellformed q1 /\
    point_G2_wellformed q2 /\
    point_oncurve p1 /\
    point_oncurve p2 /\
    point_oncurve_G2 q1 /\
    point_oncurve_G2 q2 /\
    is_some (ecPairing_precompile (((FieldQ.inF (to_uint p1.`1)), (FieldQ.inF (to_uint p1.`2))), ((FieldQ.inF (to_uint q1.`1.`1), FieldQ.inF (to_uint q1.`1.`2)), (FieldQ.inF (to_uint q1.`2.`1), FieldQ.inF (to_uint q1.`2.`2)))) (((FieldQ.inF (to_uint p2.`1)), (FieldQ.inF (to_uint p2.`2))), ((FieldQ.inF (to_uint q2.`1.`1), FieldQ.inF (to_uint q2.`1.`2)), (FieldQ.inF (to_uint q2.`2.`1), FieldQ.inF (to_uint q2.`2.`2))))).

  lemma ecPairing_precomp_is_some_of_should_succeed (p1 p2 : uint256 * uint256) (q1 q2 : (uint256*uint256) * (uint256*uint256)) :
    staticcall_ec_pairing_should_succeed p1 p2 q1 q2 =>
    is_some
    (ecPairing_precompile (((FieldQ.inF (to_uint p1.`1)), (FieldQ.inF (to_uint p1.`2))), ((FieldQ.inF (to_uint q1.`1.`1), FieldQ.inF (to_uint q1.`1.`2)), (FieldQ.inF (to_uint q1.`2.`1), FieldQ.inF (to_uint q1.`2.`2)))) (((FieldQ.inF (to_uint p2.`1)), (FieldQ.inF (to_uint p2.`2))), ((FieldQ.inF (to_uint q2.`1.`1), FieldQ.inF (to_uint q2.`1.`2)), (FieldQ.inF (to_uint q2.`2.`1), FieldQ.inF (to_uint q2.`2.`2))))). progress. smt (). qed.

  lemma ecPairing_precomp_is_none_of_should_not_succeed (p1 p2 : uint256 * uint256) (q1 q2 : (uint256*uint256) * (uint256*uint256)) :
    ((W256.to_uint p1.`1) < FieldQ.p /\ W256.to_uint p1.`2 < FieldQ.p /\
     (W256.to_uint p2.`1) < FieldQ.p /\ W256.to_uint p2.`2 < FieldQ.p /\
     (W256.to_uint q1.`1.`1) < FieldQ.p /\ W256.to_uint q1.`1.`2 < FieldQ.p /\
     (W256.to_uint q1.`2.`1) < FieldQ.p /\ W256.to_uint q1.`2.`2 < FieldQ.p /\
     (W256.to_uint q2.`1.`1) < FieldQ.p /\ W256.to_uint q2.`1.`2 < FieldQ.p /\
     (W256.to_uint q2.`2.`1) < FieldQ.p /\ W256.to_uint q2.`2.`2 < FieldQ.p /\
    ! (staticcall_ec_pairing_should_succeed p1 p2 q1 q2)) =>
    is_none
   (ecPairing_precompile (((FieldQ.inF (to_uint p1.`1)), (FieldQ.inF (to_uint p1.`2))), ((FieldQ.inF (to_uint q1.`1.`1), FieldQ.inF (to_uint q1.`1.`2)), (FieldQ.inF (to_uint q1.`2.`1), FieldQ.inF (to_uint q1.`2.`2)))) (((FieldQ.inF (to_uint p2.`1)), (FieldQ.inF (to_uint p2.`2))), ((FieldQ.inF (to_uint q2.`1.`1), FieldQ.inF (to_uint q2.`1.`2)), (FieldQ.inF (to_uint q2.`2.`1), FieldQ.inF (to_uint q2.`2.`2))))).
   progress.
           have H12 :
       (
         ! point_wellformed p1 \/
         ! point_wellformed p2 \/
         ! point_oncurve p1 \/
         ! point_oncurve p2 \/
         ! point_G2_wellformed q1 \/
         ! point_G2_wellformed q2 \/
         ! point_oncurve_G2 q1 \/
         ! point_oncurve_G2 q2 \/
         ! is_some ((ecPairing_precompile (((FieldQ.inF (to_uint p1.`1)), (FieldQ.inF (to_uint p1.`2))), ((FieldQ.inF (to_uint q1.`1.`1), FieldQ.inF (to_uint q1.`1.`2)), (FieldQ.inF (to_uint q1.`2.`1), FieldQ.inF (to_uint q1.`2.`2)))) (((FieldQ.inF (to_uint p2.`1)), (FieldQ.inF (to_uint p2.`2))), ((FieldQ.inF (to_uint q2.`1.`1), FieldQ.inF (to_uint q2.`1.`2)), (FieldQ.inF (to_uint q2.`2.`1), FieldQ.inF (to_uint q2.`2.`2))))))
       ). smt ().
   case H12.
   progress. rewrite /point_wellformed in H12.      
   have H13 : (p1.`1 <> p1.`1 %% (of_int FieldQ.p)%W256 \/ p1.`2 <> p1.`2 %% (of_int FieldQ.p)%W256). smt ().
   rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress.  exact H.
   rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress.   exact H0. smt ().    
   progress. rewrite /point_wellformed in H12.
   case H12.
   progress. rewrite /point_wellformed in H12.
   have H13 : (p2.`1 <> p2.`1 %% (of_int FieldQ.p)%W256 \/ p2.`2 <> p2.`2 %% (of_int FieldQ.p)%W256). smt ().    
   rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress.   exact H1.
   rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress.   exact H2. smt ().    
   progress. rewrite /point_wellformed in H12.
   case H12.
   progress. rewrite /point_oncurve in H12.
   apply is_none_of_eq_none.
   apply ecPairing_fail.
   smt().
   move => H12.    
   case H12.
   progress.
   rewrite /point_oncurve in H12.
   apply is_none_of_eq_none.
   apply ecPairing_fail.
   smt().
   progress.     
   case H12. progress. rewrite /point_G2_wellformed in H12.
   have H13 : (q1.`1.`1 <> q1.`1.`1 %% (of_int FieldQ.p)%W256 \/
        q1.`1.`2 <> q1.`1.`2 %% (of_int FieldQ.p)%W256 \/
        q1.`2.`1 <> q1.`2.`1 %% (of_int FieldQ.p)%W256 \/
           q1.`2.`2 <> q1.`2.`2 %% (of_int FieldQ.p)%W256). smt ().
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress.   exact H3.
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress.  exact H4.
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress. exact H5.
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress. exact H6. smt().
           progress. case H12.
           progress. rewrite /point_G2_wellformed in H12.
   have H13 : (q2.`1.`1 <> q2.`1.`1 %% (of_int FieldQ.p)%W256 \/
        q2.`1.`2 <> q2.`1.`2 %% (of_int FieldQ.p)%W256 \/
        q2.`2.`1 <> q2.`2.`1 %% (of_int FieldQ.p)%W256 \/
           q2.`2.`2 <> q2.`2.`2 %% (of_int FieldQ.p)%W256). smt ().
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress. exact H7.
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress. exact H8.
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress. exact H9.
           rewrite uint256_mod_eq_of_lt in H13. apply uint256_lt_of_lt. rewrite to_uint_small. progress. smt (@EllipticCurve). rewrite -Constants.q_eq_fieldq_p. rewrite /Constants.Q. progress. exact H10. smt().
   progress. case H12.
   progress. progress. rewrite /point_oncurve_G2 in H12.
   apply is_none_of_eq_none.
   apply ecPairing_fail.
           progress. smt().
   progress. case H12. progress. progress. progress. rewrite /point_oncurve_G2 in H12.
   apply is_none_of_eq_none.
   apply ecPairing_fail.
           progress. smt().
           progress. smt().
     qed.

     lemma staticcall_ec_pairing_pspec (memory: mem) (p1 p2 : uint256 * uint256) (q1 q2 : (uint256*uint256) * (uint256*uint256)) (argOff retOff: uint256):
    phoare [ Primops.staticcall :
      arg = (gas, W256.of_int 8, argOff, W256.of_int 384, retOff, W256.of_int 32) /\
      Primops.memory = memory /\
      p1.`1 = PurePrimops.mload memory argOff /\
      p1.`2 = PurePrimops.mload memory (argOff + W256.of_int 32) /\
      q1.`1.`1 = PurePrimops.mload memory (argOff + W256.of_int 64) /\
      q1.`1.`2 = PurePrimops.mload memory (argOff + W256.of_int 96) /\
      q1.`2.`1 = PurePrimops.mload memory (argOff + W256.of_int 128) /\
      q1.`2.`2 = PurePrimops.mload memory (argOff + W256.of_int 160) /\
      p2.`1 = PurePrimops.mload memory (argOff + W256.of_int 192) /\
      p2.`2 = PurePrimops.mload memory (argOff + W256.of_int 224) /\
      q2.`1.`1 = PurePrimops.mload memory (argOff + W256.of_int 256) /\
      q2.`1.`2 = PurePrimops.mload memory (argOff + W256.of_int 288) /\
      q2.`2.`1 = PurePrimops.mload memory (argOff + W256.of_int 320) /\
      q2.`2.`2 = PurePrimops.mload memory (argOff + W256.of_int 352)
      ==>
      ((staticcall_ec_pairing_should_succeed p1 p2 q1 q2) => (
        res = W256.one /\
        Primops.memory = PurePrimops.mstore
            memory
            retOff
            (ecPairing_precompile_unsafe_cast p1 p2 q1 q2)
      )) /\
      ((!staticcall_ec_pairing_should_succeed p1 p2 q1 q2) => res = W256.zero /\ Primops.memory = memory)
    ] = 1%r.
    proof.
      proc.

      inline *. wp. skip. progress.
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). 
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256). smt (@Utils @W256).
      smt (@Utils @W256). smt (@Utils @W256).
      case H15. progress. 
      rewrite /staticcall_ec_pairing_should_succeed /point_oncurve in H16. rewrite -H -H0 in H15. smt().
      progress. case H15. progress. rewrite /staticcall_ec_pairing_should_succeed /point_oncurve in H16. rewrite -H5 -H6 in H15. smt().
      progress. case H15. progress. rewrite /staticcall_ec_pairing_should_succeed /point_oncurve_G2 in H16. rewrite -H1 -H2 -H3 -H4 in H15. smt().
      progress. rewrite /staticcall_ec_pairing_should_succeed /point_oncurve_G2 in H16. rewrite -H7 -H8 -H9 -H10 in H15. smt().
      rewrite /staticcall_ec_pairing_should_succeed in H17.
      smt().
      rewrite /staticcall_ec_pairing_should_succeed in H17. smt().
      have Hhh := ecPairing_precomp_is_none_of_should_not_succeed p1 p2 q1 q2.
      rewrite -H -H0 -H1 -H2 -H3 -H4 -H5 -H6 -H7 -H8 -H9 -H10 in H16. smt().
      have Hhh := ecPairing_precomp_is_none_of_should_not_succeed p1 p2 q1 q2.
      rewrite -H -H0 -H1 -H2 -H3 -H4 -H5 -H6 -H7 -H8 -H9 -H10 in H16. smt().
      have Hhh := ecPairing_precomp_is_none_of_should_not_succeed p1 p2 q1 q2.
      rewrite -H -H0 -H1 -H2 -H3 -H4 -H5 -H6 -H7 -H8 -H9 -H10 in H16. smt().
  qed.
     
end ConcretePrimops.
