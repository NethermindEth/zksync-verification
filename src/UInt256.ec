pragma Goals:printall.

require export Int IntDiv JWord.

type uint256 = W256.t.

abbrev (%%) (m d : uint256) = W256.\umod m d.
abbrev (<)  (a b : uint256) = W256.\ult a b.
