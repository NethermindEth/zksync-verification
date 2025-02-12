pragma Goals:printall.

require import AllCore.
require        EllipticCurve.
require import Field.
require import Int.
require import IntDiv.
require import UInt256.
require        VerifierConsts.

op Q : int = 21888242871839275222246405745257275088696311157297823662689037894645226208583 axiomatized by qE.
op R : int = 21888242871839275222246405745257275088548364400416034343698204186575808495617 axiomatized by rE.

lemma Q_int: Q = W256.to_uint VerifierConsts.Q_MOD
    by rewrite /VerifierConsts.Q_MOD W256.of_uintK qE pmod_small; [trivial | reflexivity].
lemma R_int: R = W256.to_uint VerifierConsts.R_MOD
    by rewrite /VerifierConsts.R_MOD W256.of_uintK rE pmod_small; [trivial | reflexivity].

axiom order_g : EllipticCurve.G.order = R.
axiom q_eq_fieldq_p: Q = FieldQ.p.
axiom r_eq_fieldr_p: R = FieldR.p.    
lemma prime_q : prime Q by rewrite q_eq_fieldq_p; exact FieldQ.prime_p.
lemma prime_r : prime R by rewrite r_eq_fieldr_p; exact FieldR.prime_p.

(* 0x1dba8b5bdd64ef6ce29a9039aca3c0e524395c43b9227b96c75090cc6cc7ec97 *)
op OMEGA : int = 13446667982376394161563610564587413125564757801019538732601045199901075958935 axiomatized by omegaE.

(* 0x4000000 2^26 *)
op DOMAIN_SIZE : int = 67108864 axiomatized by domain_sizeE.

lemma OMEGA_int: OMEGA = W256.to_uint VerifierConsts.OMEGA
    by rewrite /VerifierConsts.OMEGA W256.of_uintK omegaE pmod_small; [trivial | reflexivity].
lemma DOMAIN_SIZE_int: DOMAIN_SIZE = W256.to_uint VerifierConsts.DOMAIN_SIZE
    by rewrite /VerifierConsts.DOMAIN_SIZE W256.of_uintK domain_sizeE pmod_small; [trivial | reflexivity].

op NON_RESIDUE_0: int = 5.
op NON_RESIDUE_1: int = 7.
op NON_RESIDUE_2: int = 10.

lemma non_residue_0_int: W256.to_uint VerifierConsts.NON_RESIDUES_0 = NON_RESIDUE_0
  by rewrite /VerifierConsts.NON_RESIDUES_0 W256.of_uintK /NON_RESIDUE_0 pmod_small; [trivial | reflexivity].
lemma non_residue_1_int: W256.to_uint VerifierConsts.NON_RESIDUES_1 = NON_RESIDUE_1
  by rewrite /VerifierConsts.NON_RESIDUES_1 W256.of_uintK /NON_RESIDUE_1 pmod_small; [trivial | reflexivity].
lemma non_residue_2_int: W256.to_uint VerifierConsts.NON_RESIDUES_2 = NON_RESIDUE_2
  by rewrite /VerifierConsts.NON_RESIDUES_2 W256.of_uintK /NON_RESIDUE_2 pmod_small; [trivial | reflexivity].

op OMEGAFr = FieldR.inF OMEGA axiomatized by omegaFrE.
op DOMAIN_SIZEFr = FieldR.inF DOMAIN_SIZE axiomatized by domain_sizeFrE.

lemma omega_eq_omegaFr : FieldR.asint OMEGAFr = OMEGA. 
proof.
  rewrite omegaFrE FieldR.inFK /OMEGA -r_eq_fieldr_p /R. progress. 
qed.

lemma domain_eq_domainFr : FieldR.asint DOMAIN_SIZEFr = DOMAIN_SIZE.
proof.
  rewrite domain_sizeFrE FieldR.inFK /DOMAIN_SIZE -r_eq_fieldr_p /R. progress.
qed.

op G2_ELEMENT_0: ((int*int) * (int*int)) = (
  (
    11559732032986387107991004021392285783925812861821192530917403151452391805634,
    10857046999023057135944570762232829481370756359578518086990519993285655852781
  ),
  (
    4082367875863433681332203403145435568316851327593401208105741076214120093531,
    8495653923123431417604973247489272438418190587263600148770280649306958101930
  )
).

op G2_ELEMENT_1: ((int*int) * (int*int)) = (
  (
    17212635814319756364507010169094758005397460366678210664966334781961899574209,
    496075682290949347282619629729389528669750910289829251317610107342504362928
  ),
  (
    2255182984359105691812395885056400739448730162863181907784180250290003009508,
    15828724851114720558251891430452666121603726704878231219287131634746610441813
  )
).

lemma G2_element_0_int: G2_ELEMENT_0 = (
  (W256.to_uint VerifierConsts.G2_ELEMENTS_0_X1, W256.to_uint VerifierConsts.G2_ELEMENTS_0_X2),
  (W256.to_uint VerifierConsts.G2_ELEMENTS_0_Y1, W256.to_uint VerifierConsts.G2_ELEMENTS_0_Y2)
). proof.
  rewrite /G2_ELEMENT_0 /VerifierConsts.G2_ELEMENTS_0_X1 /VerifierConsts.G2_ELEMENTS_0_X2 /VerifierConsts.G2_ELEMENTS_0_Y1 /VerifierConsts.G2_ELEMENTS_0_Y2.
  by progress.
qed.

lemma G2_element_1_int: G2_ELEMENT_1 = (
  (W256.to_uint VerifierConsts.G2_ELEMENTS_1_X1, W256.to_uint VerifierConsts.G2_ELEMENTS_1_X2),
  (W256.to_uint VerifierConsts.G2_ELEMENTS_1_Y1, W256.to_uint VerifierConsts.G2_ELEMENTS_1_Y2)
). proof.
  rewrite /G2_ELEMENT_1 /VerifierConsts.G2_ELEMENTS_1_X1 /VerifierConsts.G2_ELEMENTS_1_X2 /VerifierConsts.G2_ELEMENTS_1_Y1 /VerifierConsts.G2_ELEMENTS_1_Y2.
  by progress.
qed.

op G2_ELEMENT_0_G: EllipticCurve.g.
op G2_ELEMENT_1_G: EllipticCurve.g.
axiom G2_ELEMENT_0_G_aspoint_1_1: G2_ELEMENT_0.`1.`1 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_0_G).`1.`1.
axiom G2_ELEMENT_0_G_aspoint_1_2: G2_ELEMENT_0.`1.`2 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_0_G).`1.`2.
axiom G2_ELEMENT_0_G_aspoint_2_1: G2_ELEMENT_0.`2.`1 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_0_G).`2.`1.
axiom G2_ELEMENT_0_G_aspoint_2_2: G2_ELEMENT_0.`2.`2 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_0_G).`2.`2.
axiom G2_ELEMENT_1_G_aspoint_1_1: G2_ELEMENT_1.`1.`1 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_1_G).`1.`1.
axiom G2_ELEMENT_1_G_aspoint_1_2: G2_ELEMENT_1.`1.`2 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_1_G).`1.`2.
axiom G2_ELEMENT_1_G_aspoint_2_1: G2_ELEMENT_1.`2.`1 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_1_G).`2.`1.
axiom G2_ELEMENT_1_G_aspoint_2_2: G2_ELEMENT_1.`2.`2 = FieldQ.asint (EllipticCurve.aspoint_G2 G2_ELEMENT_1_G).`2.`2.
