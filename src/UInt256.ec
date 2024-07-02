pragma Goals:printall.

require export Int IntDiv JWord.

type uint256 = W256.t.

abbrev (%%) (m d : uint256) = W256.\umod m d.
abbrev (<)  (a b : uint256) = W256.\ult a b.
abbrev (<=) (a b : uint256) = W256.\ule a b.

op uint256_as_signed (x : uint256) : int =
  if W256.to_uint x < 340282366920938463463374607431768211456
  then W256.to_uint x
  else - (340282366920938463463374607431768211457 - (W256.to_uint x)).
op bool_of_uint256 (x : uint256) : bool = x <> W256.zero.

lemma neg_w256_zero_eq_w256_zero : - W256.zero = W256.zero.
    proof.
      smt (@W256).
  qed.

lemma eq_sub_of_add_eq (x y z : uint256) : x + y = z => x = z - y.
    progress.
    smt (@W256).
  qed.

lemma neq_sub_of_add_neq (x y z : uint256) : x + y <> z => x <> z - y.
    progress.
    smt (@W256).
  qed.

lemma lt_or_eq_of_lt_succ (a l : uint256) : a < l + W256.one => a < l \/ a = l.
    case (a < l).
    progress.
    progress.
    admit.
  qed.

lemma zero_of_to_uint_zero (x: uint256): to_uint x = 0 => x = W256.zero.
    proof.
      by smt(@W256).
  qed.
