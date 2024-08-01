pragma Goals:printall.

require import AllCore.
require        EllipticCurve.
require import Int.
require import IntDiv.
require import UInt256.
require        VerifierConsts.
require        VerifierVars.

op Q : int = 21888242871839275222246405745257275088696311157297823662689037894645226208583 axiomatized by qE.
op R : int = 21888242871839275222246405745257275088548364400416034343698204186575808495617 axiomatized by rE.

lemma Q_int: Q = W256.to_uint VerifierConsts.Q_MOD
    by rewrite /VerifierConsts.Q_MOD W256.of_uintK qE pmod_small; [trivial | reflexivity].
lemma R_int: R = W256.to_uint VerifierConsts.R_MOD
    by rewrite /VerifierConsts.R_MOD W256.of_uintK rE pmod_small; [trivial | reflexivity].

axiom q_eq_elliptic_curve_p: Q = EllipticCurve.p.
axiom prime_r : prime R.

(* 0x1dba8b5bdd64ef6ce29a9039aca3c0e524395c43b9227b96c75090cc6cc7ec97 *)
op OMEGA : int = 13446667982376394161563610564587413125564757801019538732601045199901075958935 axiomatized by omegaE.

(* 0x4000000 2^26 *)
op DOMAIN_SIZE : int = 67108864 axiomatized by domain_sizeE.

lemma OMEGA_int: OMEGA = W256.to_uint VerifierConsts.OMEGA
    by rewrite /VerifierConsts.OMEGA W256.of_uintK omegaE pmod_small; [trivial | reflexivity].
lemma DOMAIN_SIZE_int: DOMAIN_SIZE = W256.to_uint VerifierConsts.DOMAIN_SIZE
    by rewrite /VerifierConsts.DOMAIN_SIZE W256.of_uintK domain_sizeE pmod_small; [trivial | reflexivity].
