require import AllCore.
require import Group.
require import Int.
require import IntDiv.
require import ZModP. 
require import UInt256.

type g.

op p: int.
axiom prime_p : prime p.
axiom zero_lt_p : 0 < p.
axiom p_lt_W256_mod : p < W256.modulus.

clone ZModField with
  op p <- p
  proof prime_p by apply prime_p.

type F = ZModField.zmod.
  
clone CyclicGroup as G with type group <- g.

abbrev q = G.order.
axiom prime_q : prime q.

op aspoint_G1: g -> F * F.
op aspoint_G2: g -> (F * F) * (F * F).

axiom aspoint_G1_inj (x1 x2 : g) : aspoint_G1 x1 = aspoint_G1 x2 => x1 = x2. 
axiom aspoint_G2_inj (x1 x2 : g) : aspoint_G2 x1 = aspoint_G2 x2 => x1 = x2.

op [-] = ZModField.inv.

axiom zero_G1 : (aspoint_G1 G.e) = (ZModField.zero, ZModField.zero).
axiom neg_G1_fst (x : g) : fst (aspoint_G1 (G.inv x)) = fst (aspoint_G1 x).
axiom neg_G1_snd (x : g) : snd (aspoint_G1 (G.inv x)) = (- (snd (aspoint_G1 x))).

op on_curve : F * F -> bool.

axiom aspoint_on_curve (p : g) : on_curve (aspoint_G1 p).
axiom on_curve_as_point (x y : F) : on_curve (x, y) => exists p, aspoint_G1 p = (x, y).

(* TODO: Axioms for G2. *)

op ( + ) = G.( * ).
op ( * ) x y = G.( ^ ) y x.

op ecAdd_precompile (x1 y1 x2 y2 : F) : (F * F) option.  
op ecMul_precompile (x y : F) (s : int) : (F * F) option.

axiom ecAdd_def (x1 y1 x2 y2 : F) (p1 p2 : g) :
  aspoint_G1 p1 = (x1, y1)
    => aspoint_G1 p2 = (x2, y2)
      => Some (aspoint_G1 (p1 + p2)) = ecAdd_precompile x1 y1 x2 y2.

axiom ecAdd_fail (x1 y1 x2 y2 : F) :
  !(on_curve (x1, y1)) \/ !(on_curve (x2, y2)) => ecAdd_precompile x1 y1 x2 y2 = None.

axiom ecMul_def (x y : F) (s : int) (p : g):
  aspoint_G1 p = (x, y)
    => Some (aspoint_G1 (s * p)) = ecMul_precompile x y s.

axiom ecMul_fail (x y : F) (s : int) :
  !(on_curve (x, y)) => ecMul_precompile x y s = None.

lemma ec_add_result_on_curve (x1 y1 x2 y2 x3 y3 : F):
    ecAdd_precompile x1 y1 x2 y2 = Some (x3, y3) =>
    on_curve (x3, y3).
    progress.
    have J : on_curve (x1, y1) /\ on_curve (x2, y2). smt.
    have J1 : exists p, aspoint_G1 p = (x1, y1). smt.
    have J2 : exists p, aspoint_G1 p = (x2, y2). smt.
    case J2. move=>p2 J2.
    case J1. move=>p1 J1.
    have H' := ecAdd_def x1 y1 x2 y2 p1 p2 J1 J2.
    rewrite H in H'.
    have H'' : aspoint_G1 (p1 + p2) = (x3, y3). smt ().
    rewrite -H''. exact (aspoint_on_curve (p1 + p2)).
  qed.
    
lemma ec_mul_result_on_curve (x1 y1 x2 y2 : F) (s : int) :
    ecMul_precompile x1 y1 s = Some (x2, y2) =>
    on_curve (x2, y2).
    progress.
    have J : on_curve (x1, y1). smt.
    have J1 : exists p, aspoint_G1 p = (x1, y1). smt.
    case J1. move=> p J1.
    have H' := ecMul_def x1 y1 s p J1.
    rewrite H in H'.
    have H'' : aspoint_G1 (s * p) = (x2, y2). smt ().
    rewrite -H''. exact (aspoint_on_curve (s * p)).
  qed.
    
    

op F_to_int_point (p : F * F) : (int * int) = (ZModField.asint (fst p), ZModField.asint (snd p)).
