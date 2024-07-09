pragma Goals:printall.

require        Constants.
require import PurePrimops.
require import UInt256.
require import Verifier.
require import YulPrimops.

module PermutationQuotientContribution = {
  proc low(): uint256 = {
    var usr_res, _3, _5, usr_gamma, usr_beta, usr_factorMultiplier, _9, _11, _13, _15, _17, _19, tmp280, _22, usr_l0AtZ, tmp282;
    _3 <@ Primops.mload(W256.of_int 2848);
    _5 <@ Primops.mload(W256.of_int 3680);
    usr_res <- (PurePrimops.mulmod _5 _3 (W256.of_int Constants.R));
    usr_gamma <@ Primops.mload(W256.of_int 3584);
    usr_beta <@ Primops.mload(W256.of_int 3552);
    _9 <@ Primops.mload(W256.of_int 2752);
    usr_factorMultiplier <- (PurePrimops.mulmod _9 usr_beta (W256.of_int Constants.R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int Constants.R));
    _11 <@ Primops.mload(W256.of_int 2560);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _11 (W256.of_int Constants.R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int Constants.R));
    _13 <@ Primops.mload(W256.of_int 2784);
    usr_factorMultiplier <- (PurePrimops.mulmod _13 usr_beta (W256.of_int Constants.R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int Constants.R));
    _15 <@ Primops.mload(W256.of_int 2592);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _15 (W256.of_int Constants.R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int Constants.R));
    _17 <@ Primops.mload(W256.of_int 2816);
    usr_factorMultiplier <- (PurePrimops.mulmod _17 usr_beta (W256.of_int Constants.R));
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier usr_gamma (W256.of_int Constants.R));
    _19 <@ Primops.mload(W256.of_int 2624);
    usr_factorMultiplier <- (PurePrimops.addmod usr_factorMultiplier _19 (W256.of_int Constants.R));
    usr_res <- (PurePrimops.mulmod usr_res usr_factorMultiplier (W256.of_int Constants.R));
    tmp280 <@ Primops.mload(W256.of_int 2656);
    _22 <- (PurePrimops.addmod tmp280 usr_gamma (W256.of_int Constants.R));
    usr_res <- ((W256.of_int Constants.R) - (PurePrimops.mulmod usr_res _22 (W256.of_int Constants.R)));
    usr_l0AtZ <@ Primops.mload((W256.of_int 4128));
    tmp282 <@ Primops.mload((W256.of_int 3712));
    usr_l0AtZ <- (PurePrimops.mulmod usr_l0AtZ tmp282 (W256.of_int Constants.R));
    usr_res <- (PurePrimops.addmod usr_res ((W256.of_int Constants.R) - usr_l0AtZ) (W256.of_int Constants.R));
    return usr_res;
  }
}.

lemma permutationQuotientContribution_extracted_equiv_low:
    equiv [
      Verifier_1261.usr_permutationQuotientContribution ~ PermutationQuotientContribution.low:
      ={arg, glob PermutationQuotientContribution} ==>
      ={res, glob PermutationQuotientContribution}
    ].
    proof.
    proc.
      wp.
      inline Primops.mload.
      wp.
      skip.
      rewrite /Constants.R.
      by progress.
    qed.
