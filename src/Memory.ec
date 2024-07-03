require import UInt256.
require export CoreMap SmtMap.

type mem = (uint256, uint256) map.
pred mem_wellformed (memory: mem) = forall (idx: uint256), memory.[idx] <= W256.masklsb 8.

lemma write_byte_maintains_wellformed (memory: mem) (idx val: uint256):
    val < W256.masklsb 8 =>
    mem_wellformed memory =>
    mem_wellformed (memory.[idx <- val]).
    proof.
      progress.
      smt ().
    qed.
