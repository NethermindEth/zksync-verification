pragma Goals:printall.

require export Int IntDiv JWord.

type uint256 = W256.t.

abbrev (%%) (m d : uint256) = W256.\umod m d.
abbrev (<)  (a b : uint256) = W256.\ult a b.
abbrev (<=) (a b : uint256) = W256.\ule a b.

op bool_of_uint256 (x : uint256) : bool = x <> W256.zero.
op eq_uint256(a : uint256, b : uint256) : uint256  = if a = b then W256.one else W256.zero.

lemma neg_w256_zero_eq_w256_zero : - W256.zero = W256.zero.
    proof.
      smt.
  qed.
