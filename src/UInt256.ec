pragma Goals:printall.

require import AllCore.
require export Int IntDiv JWord.

type uint8 = W8.t. (*specifically used for storing bytes in the memory map*)
type uint256 = W256.t.

abbrev (%%) (m d : uint256) = W256.\umod m d.
abbrev (<)  (a b : uint256) = W256.\ult a b.
abbrev (<=) (a b : uint256) = W256.\ule a b.

op uint256_as_signed (x : uint256) : int =
  if W256.to_uint x < 340282366920938463463374607431768211456
  then W256.to_uint x
  else - (340282366920938463463374607431768211457 - (W256.to_uint x)).
op bool_of_uint256 (x : uint256) : bool = x <> W256.zero.

(* op try_u256_to_u8 (x: uint256) : uint8 option =
  if W256.to_uint x < (2^8)
  then Some (W8.of_int (W256.to_uint x))
  else None. *)

lemma neg_w256_zero_eq_w256_zero : - W256.zero = W256.zero.
    proof.
      smt (@W256).
  qed.

lemma eq_sub_of_add_eq (x y z : uint256) : x + y = z => x = z - y.
  proof.
    progress.
    smt (@W256).
  qed.

lemma neq_sub_of_add_neq (x y z : uint256) : x + y <> z => x <> z - y.
  proof.
    progress.
    smt (@W256).
  qed.

lemma uint256_lt_or_eq_of_le (a l : uint256) : a <= l => a < l \/ a = l.
    progress. smt.
  qed.
  
lemma lt_or_eq_of_lt_succ (a l : uint256) : a < l + W256.one => a < l \/ a = l.
  proof.
    case (a < l).
    progress.
    progress.
    have H' : a <= l. smt (@W256).
    have H'' : a < l \/ a = l. apply uint256_lt_or_eq_of_le. exact H'.
    smt ().
  qed.

lemma zero_of_to_uint_zero (x: uint256): to_uint x = 0 => x = W256.zero.
    proof.
      by smt(@W256).
  qed.
