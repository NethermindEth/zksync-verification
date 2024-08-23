require import AllCore.
require import Field.
require import Group.
require import Int.
require import IntDiv.
require import ZModP. 
require import UInt256.


type g.
  
clone CyclicGroup as G with type group <- g.

abbrev q = G.order.

op aspoint_G1: g -> FieldQ.F * FieldQ.F.
op aspoint_G2: g -> (FieldQ.F * FieldQ.F) * (FieldQ.F * FieldQ.F).

axiom aspoint_G1_inj (x1 x2 : g) : aspoint_G1 x1 = aspoint_G1 x2 => x1 = x2. 
axiom aspoint_G2_inj (x1 x2 : g) : aspoint_G2 x1 = aspoint_G2 x2 => x1 = x2.

op [-] = FieldQ.([-]).

axiom zero_G1 : (aspoint_G1 G.e) = (FieldQ.zero, FieldQ.zero).
axiom neg_G1_fst (x : g) : fst (aspoint_G1 (G.inv x)) = fst (aspoint_G1 x).
axiom neg_G1_snd (x : g) : snd (aspoint_G1 (G.inv x)) = (- (snd (aspoint_G1 x))).

op on_curve : FieldQ.F * FieldQ.F -> bool.

axiom aspoint_on_curve (p : g) : on_curve (aspoint_G1 p).
axiom on_curve_as_point (x y : FieldQ.F) : on_curve (x, y) => exists p, aspoint_G1 p = (x, y).

(* specific to the curve we're using *)
axiom x_non_zero_y_zero_not_on_curve (x: FieldQ.F) : x <> FieldQ.zero => !on_curve (x, FieldQ.zero).


axiom zero_G2 : (aspoint_G2 G.e) = ((FieldQ.zero, FieldQ.zero), (FieldQ.zero, FieldQ.zero)).
axiom neg_G2_fst (x : g) : fst (aspoint_G2 (G.inv x)) = fst (aspoint_G2 x).
axiom neg_G2_snd (x : g) : snd (aspoint_G2 (G.inv x)) = (-(fst (snd (aspoint_G2 x))), -(snd (snd (aspoint_G2 x)))).

op on_curve_G2 : (FieldQ.F * FieldQ.F) * (FieldQ.F * FieldQ.F) -> bool.

axiom aspoint_on_curve_G2 (p : g) : on_curve_G2 (aspoint_G2 p).
axiom on_curve_as_point_G2 (x1 y1 x2 y2 : FieldQ.F) : on_curve_G2 ((x1, y1), (x2, y2)) => exists p, aspoint_G2 p = ((x1, y1), (x2, y2)).

op ( + ) = G.( * ).
op ( * ) (x: FieldR.F, y: g) = G.( ^ ) y (FieldR.asint x).

op e: g -> g -> g.

axiom e_bilin (m n : FieldR.F) (x1 x2 : g) : e (m * x1) (n * x2) = (FieldR.(+) m n) * (e x1 x2).
axiom e_non_deg_1 (x : g) : x <> G.e => exists y, e x y <> G.e.
axiom e_non_deg_2 (y : g) : y <> G.e => exists x, e x y <> G.e.

op ecAdd_precompile (x1 y1 x2 y2 : FieldQ.F) : (FieldQ.F * FieldQ.F) option.  
op ecMul_precompile (x y : FieldQ.F) (s : int) : (FieldQ.F * FieldQ.F) option.
op ecPairing_precompile (input1 input2 : ((FieldQ.F *  FieldQ.F) * ((FieldQ.F * FieldQ.F) * (FieldQ.F * FieldQ.F)))) : bool option.

axiom ecAdd_def (x1 y1 x2 y2 : FieldQ.F) (p1 p2 : g) :
  aspoint_G1 p1 = (x1, y1)
    => aspoint_G1 p2 = (x2, y2)
      => Some (aspoint_G1 (p1 + p2)) = ecAdd_precompile x1 y1 x2 y2.

axiom ecAdd_fail (x1 y1 x2 y2 : FieldQ.F) :
  !(on_curve (x1, y1)) \/ !(on_curve (x2, y2)) => ecAdd_precompile x1 y1 x2 y2 = None.

axiom ecMul_def (x y : FieldQ.F) (s : int) (p : g):
  aspoint_G1 p = (x, y)
    => Some (aspoint_G1 (FieldR.inF s * p)) = ecMul_precompile x y s.

axiom ecMul_fail (x y : FieldQ.F) (s : int) :
  !(on_curve (x, y)) => ecMul_precompile x y s = None.

axiom ecPairing_def (input1 input2 : ((FieldQ.F * FieldQ.F) * ((FieldQ.F * FieldQ.F) * (FieldQ.F * FieldQ.F)))) (p1 p2 q1 q2: g) :
  aspoint_G1 p1 = fst input1
    => aspoint_G1 p2 = fst input2
    => aspoint_G2 q1 = snd input1
    => aspoint_G2 q2 = snd input2
    => Some (e (p1 + p2) (q1 + q2) = G.e) = ecPairing_precompile input1 input2.

axiom ecPairing_fail (input1 input2 : ((FieldQ.F * FieldQ.F) * ((FieldQ.F * FieldQ.F) * (FieldQ.F * FieldQ.F)))):
  !(on_curve (fst input1)) \/ !(on_curve (fst input2)) \/ !(on_curve_G2 (snd input1)) \/ !(on_curve_G2 (snd input2)) => ecPairing_precompile input1 input2 = None.    
    
lemma ec_add_result_on_curve (x1 y1 x2 y2 x3 y3 : FieldQ.F):
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
    
lemma ec_mul_result_on_curve (x1 y1 x2 y2 : FieldQ.F) (s : int) :
    ecMul_precompile x1 y1 s = Some (x2, y2) =>
    on_curve (x2, y2).
    progress.
    have J : on_curve (x1, y1). smt.
    have J1 : exists p, aspoint_G1 p = (x1, y1). smt.
    case J1. move=> p J1.
    have H' := ecMul_def x1 y1 s p J1.
    rewrite H in H'.
    have H'' : aspoint_G1 (FieldR.inF s * p) = (x2, y2). smt ().
    rewrite -H''. exact (aspoint_on_curve (FieldR.inF s * p)).
  qed.
    
op F_to_int_point (p : FieldQ.F * FieldQ.F) : (int * int) = (FieldQ.asint (fst p), FieldQ.asint (snd p)).

lemma F_to_int_point_inzmod_1 (p: FieldQ.F*FieldQ.F): FieldQ.inF (F_to_int_point p).`1 = p.`1.
    proof. rewrite /F_to_int_point. simplify. exact FieldQ.asintK. qed.
lemma F_to_int_point_inzmod_2 (p: FieldQ.F*FieldQ.F): FieldQ.inF (F_to_int_point p).`2 = p.`2.
    proof. rewrite /F_to_int_point. simplify. exact FieldQ.asintK. qed.
  
lemma F_to_int_point_mod_Q_1 (point: FieldQ.F*FieldQ.F): (F_to_int_point point).`1 %% FieldQ.p = (F_to_int_point point).`1.
    proof.
      rewrite /F_to_int_point. simplify. rewrite pmod_small. progress.
      exact FieldQ.ge0_asint.
      exact FieldQ.gtp_asint.
      reflexivity.
    qed.
lemma F_to_int_point_mod_Q_2 (point: FieldQ.F*FieldQ.F): (F_to_int_point point).`2 %% FieldQ.p = (F_to_int_point point).`2.
    proof.
      rewrite /F_to_int_point. simplify. rewrite pmod_small. progress.
      exact FieldQ.ge0_asint.
      exact FieldQ.gtp_asint.
      reflexivity.
  qed.

lemma F_to_int_point_1_ge_zero (point: FieldQ.F*FieldQ.F): 0 <= (F_to_int_point point).`1.
    proof.
      rewrite /F_to_int_point.
      progress.
      exact FieldQ.ge0_asint.
    qed.
lemma F_to_int_point_2_ge_zero (point: FieldQ.F*FieldQ.F): 0 <= (F_to_int_point point).`2.
    proof.
      rewrite /F_to_int_point.
      progress.
      exact FieldQ.ge0_asint.
  qed.
lemma F_to_int_point_1_lt_p (point: FieldQ.F*FieldQ.F): (F_to_int_point point).`1 < FieldQ.p.
    proof.
      rewrite /F_to_int_point.
      progress.
      exact FieldQ.gtp_asint.
    qed.
lemma F_to_int_point_2_lt_p (point: FieldQ.F*FieldQ.F): (F_to_int_point point).`2 < FieldQ.p.
    proof.
      rewrite /F_to_int_point.
      progress.
      exact FieldQ.gtp_asint.
    qed.
