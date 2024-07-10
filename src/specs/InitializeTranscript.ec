require        Constants.
require import GetTranscriptChallenge.
require import Modexp.
require import PurePrimops.
require import UInt256.
require import UpdateTranscript.
require import Verifier.
require import YulPrimops.

module InitializeTranscript = {
  proc low(): unit = {
    var _2, _4, _6, _8, _10, _12, _14, _16, _18, _20, _23, _25, _27, _30, _33, _35, _37, _40, _43, _45, _47, _50, _52, _54, _56, _58, _60, _62, _64, z, _68, _71, _73, _75, _77, _79, _81, _83, _85, _87, _89, _91, _93, _95, _97, _99, _101, _103, _105, _107, _110, _112, _114, _116, _118;
    _2 <@ Primops.mload(W256.of_int 1824);
    UpdateTranscript.low(_2);
    _4 <@ Primops.mload(W256.of_int 1856);
    UpdateTranscript.low(_4);
    _6 <@ Primops.mload(W256.of_int 1888);
    UpdateTranscript.low(_6);
    _8 <@ Primops.mload(W256.of_int 1920);
    UpdateTranscript.low(_8);
    _10 <@ Primops.mload(W256.of_int 1952);
    UpdateTranscript.low(_10);
    _12 <@ Primops.mload(W256.of_int 1984);
    UpdateTranscript.low(_12);
    _14 <@ Primops.mload(W256.of_int 2016);
    UpdateTranscript.low(_14);
    _16 <@ Primops.mload(W256.of_int 2048);
    UpdateTranscript.low(_16);
    _18 <@ Primops.mload(W256.of_int 2080);
    UpdateTranscript.low(_18);
    _20 <@ GetTranscriptChallenge.low(W256.zero);
    Primops.mstore(W256.of_int 3840, _20);
    _23 <@ Primops.mload(W256.of_int 2176);
    UpdateTranscript.low(_23);
    _25 <@ Primops.mload(W256.of_int 2208);
    UpdateTranscript.low(_25);
    _27 <@ GetTranscriptChallenge.low(W256.one);
    Primops.mstore(W256.of_int 3552, _27);
    _30 <@ GetTranscriptChallenge.low(W256.of_int 2);
    Primops.mstore(W256.of_int 3584, _30);
    _33 <@ Primops.mload(W256.of_int 2112);
    UpdateTranscript.low(_33);
    _35 <@ Primops.mload(W256.of_int 2144);
    UpdateTranscript.low(_35);
    _37 <@ GetTranscriptChallenge.low(W256.of_int 3);
    Primops.mstore(W256.of_int 3872, _37);
    _40 <@ GetTranscriptChallenge.low(W256.of_int 4);
    Primops.mstore(W256.of_int 3904, _40);
    _43 <@ Primops.mload(W256.of_int 2240);
    UpdateTranscript.low(_43);
    _45 <@ Primops.mload(W256.of_int 2272);
    UpdateTranscript.low(_45);
    _47 <@ GetTranscriptChallenge.low(W256.of_int 5);
    Primops.mstore(W256.of_int 3520, _47);
    _50 <@ Primops.mload(W256.of_int 2304);
    UpdateTranscript.low(_50);
    _52 <@ Primops.mload(W256.of_int 2336);
    UpdateTranscript.low(_52);
    _54 <@ Primops.mload(W256.of_int 2368);
    UpdateTranscript.low(_54);
    _56 <@ Primops.mload(W256.of_int 2400);
    UpdateTranscript.low(_56);
    _58 <@ Primops.mload(W256.of_int 2432);
    UpdateTranscript.low(_58);
    _60 <@ Primops.mload(W256.of_int 2464);
    UpdateTranscript.low(_60);
    _62 <@ Primops.mload(W256.of_int 2496);
    UpdateTranscript.low(_62);
    _64 <@ Primops.mload(W256.of_int 2528);
    UpdateTranscript.low(_64);
    z <@ GetTranscriptChallenge.low(W256.of_int 6);
    Primops.mstore(W256.of_int 4064, z);
    _68 <@ Modexp.low(z, W256.of_int 67108864);
    Primops.mstore(W256.of_int 4192, _68);
    _71 <@ Primops.mload(W256.of_int 3072);
    UpdateTranscript.low(_71);
    _73 <@ Primops.mload(W256.of_int 2560);
    UpdateTranscript.low(_73);
    _75 <@ Primops.mload(W256.of_int 2592);
    UpdateTranscript.low(_75);
    _77 <@ Primops.mload(W256.of_int 2624);
    UpdateTranscript.low(_77);
    _79 <@ Primops.mload(W256.of_int 2656);
    UpdateTranscript.low(_79);
    _81 <@ Primops.mload(W256.of_int 2688);
    UpdateTranscript.low(_81);
    _83 <@ Primops.mload(W256.of_int 2720);
    UpdateTranscript.low(_83);
    _85 <@ Primops.mload(W256.of_int 2752);
    UpdateTranscript.low(_85);
    _87 <@ Primops.mload(W256.of_int 2784);
    UpdateTranscript.low(_87);
    _89 <@ Primops.mload(W256.of_int 2816);
    UpdateTranscript.low(_89);
    _91 <@ Primops.mload(W256.of_int 2848);
    UpdateTranscript.low(_91);
    _93 <@ Primops.mload(W256.of_int 2944);
    UpdateTranscript.low(_93);
    _95 <@ Primops.mload(W256.of_int 3008);
    UpdateTranscript.low(_95);
    _97 <@ Primops.mload(W256.of_int 3040);
    UpdateTranscript.low(_97);
    _99 <@ Primops.mload(W256.of_int 2880);
    UpdateTranscript.low(_99);
    _101 <@ Primops.mload(W256.of_int 2912);
    UpdateTranscript.low(_101);
    _103 <@ Primops.mload(W256.of_int 2976);
    UpdateTranscript.low(_103);
    _105 <@ Primops.mload(W256.of_int 3104);
    UpdateTranscript.low(_105);
    _107 <@ GetTranscriptChallenge.low(W256.of_int 7);
    Primops.mstore(W256.of_int 4000, _107);
    _110 <@ Primops.mload(W256.of_int 3136);
    UpdateTranscript.low(_110);
    _112 <@ Primops.mload(W256.of_int 3168);
    UpdateTranscript.low(_112);
    _114 <@ Primops.mload(W256.of_int 3200);
    UpdateTranscript.low(_114);
    _116 <@ Primops.mload(W256.of_int 3232);
    UpdateTranscript.low(_116);
    _118 <@ GetTranscriptChallenge.low(W256.of_int 8);
    Primops.mstore(W256.of_int 4032, _118);
    }
}.

lemma initializeTranscript_extracted_equiv_low :
    equiv [
      Verifier_1261.usr_initializeTranscript ~ InitializeTranscript.low :
      ={arg, glob InitializeTranscript} ==>
      ={res, glob InitializeTranscript}
    ].
proof.
  proc.
  inline Primops.mload Primops.mstore.
  do 9! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  seq 7 4: #pre. wp. call getTranscriptChallenge_extracted_equiv_low. wp. skip. by progress.
  do 2! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 2! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 1! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 8! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  seq 14 8: #pre. wp. call modexp_extracted_equiv_low. wp. call getTranscriptChallenge_extracted_equiv_low. wp. skip. by progress.
  do 18! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  do 1! (seq 7 4: #pre; first wp; first call getTranscriptChallenge_extracted_equiv_low; first wp; first skip; first by progress).
  do 4! (seq 5 3: #pre; first call updateTranscript_extracted_equiv_low; first wp; first skip; first by progress).
  wp. call getTranscriptChallenge_extracted_equiv_low. wp. skip. by progress.
qed.
