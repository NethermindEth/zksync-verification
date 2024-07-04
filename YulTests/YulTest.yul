object "YulTest" {
    code {
        {
            let _1 := 0
        }
    }
    object "YulTest_deployed" {
        code {
          {
                let _1 := 0
          }
          function writeReadTest(addr, value) -> r {
            mstore(addr, value)
            let _1 := mload(addr)
            r := _1
          }
          function revert_if_two(x) -> r {
            let y := add(x, 3)
            if eq(y, 5) {
              revert(0x0, 0x0)
            }
            r := y
          }
          function shifty(x, s) -> r {
            if gt(s, 256) {
              revert(0x0, 0x0)
            }
            let v1 := shl(x, s)
            let v2 := shr(x, sub(256, s))
            let v1_ := shr(v1, s)
            let v2_ := shl(v2, sub(256, s))
            r := add(v1_, v2_)
          }
          function mod_test(m) -> r {
            let mv := sub(m, 1)
            let o := mulmod(mv, mv, m)
            let z := addmod(o, mv, m)
            r := z
          }
          function mstore8test(x, y) -> r {
            mstore(0x0, 0x0)
            mstore8(0x0, x)
            mstore8(0x1, y)
            let z := mload(0x0)
            r := z
          }
          function calldata_test(ind) -> r {
            let v1 := calldataload(ind)
            let v2 := calldataload(ind)
            let r_ := eq(v1, v2)
            r := r_
          }
          function modexp_test(x, y, z) -> s, r {
            mstore(0x0, 32)
            mstore(32, 32)
            mstore(64, 32)
            mstore(96, x)
            mstore(128, y)
            mstore(160, z)
            let success := staticcall(1, 5, 0, 192, 0, 32)
            let ret := mload(0x0)
            s := success
            r := ret
          }
          function is_even(a) -> r {
            let ret := iszero(mod(a, 2))
            r := ret
          }
          function ret_test(a, b)  {
            mstore(0x0, a)
            mstore(0x20, b)
            return(0x0, 0x40)
          }
          function and_test(a, b) -> r,z {
            r := and(a, b)
            z := and(a, 0x0)
          }

        }
        data ".metadata" hex""
    }
}
