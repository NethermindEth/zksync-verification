pragma Goals:printall.
prover timeout=100.

require import AllCore.
require import Array.
require import Int.
require import IntDiv.
require import Logic.
require import PurePrimops.
require import Utils.
require export EllipticCurve.
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
    memory <- memory.[idx<-W8.of_int (W256.to_uint val)];
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
      (* TODO: relate to keccak_f *)
      var input : uint8 array;
      input <- Array.offun (fun (i: int) => memory.[off + (W256.of_int i)]) (W256.to_uint size);
      return PurePrimops.keccak256_f input;
  }

  proc staticcall(gas : uint256, addr : uint256, argOff : uint256, argSize : uint256, retOff : uint256, retSize : uint256) : uint256 = {
      var succ;
      var bsize, esize, msize : uint256;
      var base, exp, mod;
      var x1, y1, x2, y2;
      var s;
      var s_F;
      var x1_F, y1_F, x2_F, y2_F;
      var result;
      var result_unwrap;
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
            x1_F <- ZModField.inzmod (W256.to_uint x1);
            y1_F <- ZModField.inzmod (W256.to_uint y1);
            x2_F <- ZModField.inzmod (W256.to_uint x2);
            y2_F <- ZModField.inzmod (W256.to_uint y2);
            if (x1 <> x1 %% W256.of_int p \/ y1 <> y1 %% W256.of_int p \/ x2 <> x2 %% W256.of_int p \/ y2 <> y2 %% W256.of_int p) {
              succ <- W256.zero;
            } else {
              if (!(on_curve (x1_F, y1_F)) \/ !(on_curve ((x2_F, y2_F)))) {
                succ <- W256.zero;
              } else {
                result <- ecAdd_precompile x1_F y1_F x2_F y2_F;
                if (is_none result) {
                  succ <- W256.zero;
                } else {
                    result_unwrap <- odflt (ZModField.zero, ZModField.zero) result;
                    mstore(retOff, W256.of_int (ZModField.asint (fst result_unwrap)));
                    mstore(retOff + W256.of_int 32, W256.of_int (ZModField.asint (snd (result_unwrap))));
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
              x1_F <- ZModField.inzmod (W256.to_uint x1);
              y1_F <- ZModField.inzmod (W256.to_uint y1);
              s_F <- ZModField.inzmod (W256.to_uint s);
              if (x1 <> x1 %% W256.of_int p \/ y1 <> y1 %% W256.of_int p) {
                succ <- W256.zero;
              } else {
                if (!(on_curve (x1_F, y1_F))) {
                  succ <- W256.zero;
                } else {
                  result <- ecMul_precompile x1_F y1_F s_F;
                  if (is_none result) {
                    succ <- W256.zero;
                  } else {
                      result_unwrap <- odflt (ZModField.zero, ZModField.zero) result;
                      mstore(retOff, W256.of_int (ZModField.asint (fst result_unwrap)));
                      mstore(retOff + W256.of_int 32, W256.of_int (ZModField.asint (snd (result_unwrap))));
                      succ <- W256.one;
                  }                
                }
              }
            }
          } else {
            if (addr = W256.of_int 8) {
              (* TODO: ecPairing *)
              succ <- W256.zero;
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
    return PurePrimops.calldata.[W256.to_uint i];
  }

  proc calldatasize() = {
    return W256.of_int (Array.size (PurePrimops.calldata));
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
      res = PurePrimops.calldata.[W256.to_uint idx]
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
  
lemma is_none_iff_not_is_some (a: 'a option): is_none a <=> !is_some a.
    proof.
      case (a = None). smt (). smt ().
    qed.

pred point_wellformed (pnt: uint256*uint256) =
    pnt.`1 = pnt.`1 %% W256.of_int p /\
    pnt.`2 = pnt.`2 %% W256.of_int p.
pred point_oncurve (pnt: uint256*uint256) =
    on_curve ((ZModField.inzmod(to_uint pnt.`1)), (ZModField.inzmod(to_uint pnt.`2))).
pred staticcall_ec_add_should_succeed (p1 p2: uint256 * uint256) =
    point_wellformed p1 /\
    point_wellformed p2 /\
    point_oncurve p1 /\
    point_oncurve p2 /\
    is_some (ecAdd_precompile (ZModField.inzmod(to_uint p1.`1)) (ZModField.inzmod(to_uint p1.`2)) (ZModField.inzmod(to_uint p2.`1)) (ZModField.inzmod(to_uint p2.`2))).

op ecAdd_precompile_unsafe_cast (p1 p2: uint256 * uint256): (uint256*uint256) =
  let x1 = ZModField.inzmod(to_uint p1.`1) in
  let y1 = ZModField.inzmod(to_uint p1.`2) in
  let x2 = ZModField.inzmod(to_uint p2.`1) in
  let y2 = ZModField.inzmod(to_uint p2.`2) in
  let ret = ecAdd_precompile x1 y1 x2 y2 in
  let ret_unwrapped = odflt (ZModField.zero, ZModField.zero) ret in
  let x_ret = W256.of_int (ZModField.asint ret_unwrapped.`1) in
  let y_ret = W256.of_int (ZModField.asint ret_unwrapped.`2) in
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

end ConcretePrimops.
