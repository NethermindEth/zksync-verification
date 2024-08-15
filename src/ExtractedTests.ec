require import PurePrimops.
require import UInt256.
require import YulPrimops.

(* Begin YulTest *)
module YulTest = {
  proc mod_test(m : uint256): uint256 = {
    var r, mv, o, z;
    mv <- (m - (W256.of_int 1));
    o <- (PurePrimops.mulmod mv mv m);
    z <- (PurePrimops.addmod o mv m);
    r <- z;
    return r;
    }
  
  proc calldata_test(ind : uint256): uint256 = {
    var r, v1, tmp2, v2, tmp3, r_;
    tmp2 <@ Primops.calldataload(ind);
    v1 <- tmp2;
    tmp3 <@ Primops.calldataload(ind);
    v2 <- tmp3;
    r_ <- (PurePrimops.eq_uint256 v1 v2);
    r <- r_;
    return r;
    }
  
  proc revert_if_two(x : uint256): uint256 = {
    var r, y;
    y <- (x + (W256.of_int 3));
    if ((bool_of_uint256 (PurePrimops.eq_uint256 y (W256.of_int 5))))
      {
      Primops.revert((W256.of_int 0), (W256.of_int 0));
      
      }
    
    r <- y;
    return r;
    }
  
  proc is_even(a : uint256): uint256 = {
    var r, ret;
    ret <- (PurePrimops.iszero (a %% (W256.of_int 2)));
    r <- ret;
    return r;
    }
  
  proc writeReadTest(addr : uint256, value : uint256): uint256 = {
    var r, _1, tmp0;
    Primops.mstore(addr, value);
    tmp0 <@ Primops.mload(addr);
    _1 <- tmp0;
    r <- _1;
    return r;
    }
  
  proc shifty(x : uint256, s : uint256): uint256 = {
    var r, v1, v2, v1_, v2_;
    if ((bool_of_uint256 (PurePrimops.gt_uint256 s (W256.of_int 256))))
      {
      Primops.revert((W256.of_int 0), (W256.of_int 0));
      
      }
    
    v1 <- (PurePrimops.shl s x);
    v2 <- (PurePrimops.shr ((W256.of_int 256) - s) x);
    v1_ <- (PurePrimops.shr s v1);
    v2_ <- (PurePrimops.shl ((W256.of_int 256) - s) v2);
    r <- (v1_ + v2_);
    return r;
    }
  
  proc ret_test(a : uint256, b : uint256): unit = {
    Primops.mstore((W256.of_int 0), a);
    Primops.mstore((W256.of_int 32), b);
    Primops.evm_return((W256.of_int 0), (W256.of_int 64));
    }
  
  proc mstore8test(x : uint256, y : uint256): uint256 = {
    var r, z, tmp1;
    Primops.mstore((W256.of_int 0), (W256.of_int 0));
    Primops.mstore8((W256.of_int 0), x);
    Primops.mstore8((W256.of_int 1), y);
    tmp1 <@ Primops.mload((W256.of_int 0));
    z <- tmp1;
    r <- z;
    return r;
    }
  
  proc and_test(a : uint256, b : uint256): (uint256 * uint256) = {
    var r, z;
    r <- (PurePrimops.bit_and a b);
    z <- (PurePrimops.bit_and a (W256.of_int 0));
    return (r, z);
    }
  
  proc modexp_test(x : uint256, y : uint256, z : uint256): (uint256 * uint256) = {
    var s, r, success, tmp4, ret, tmp5;
    Primops.mstore((W256.of_int 0), (W256.of_int 32));
    Primops.mstore((W256.of_int 32), (W256.of_int 32));
    Primops.mstore((W256.of_int 64), (W256.of_int 32));
    Primops.mstore((W256.of_int 96), x);
    Primops.mstore((W256.of_int 128), y);
    Primops.mstore((W256.of_int 160), z);
    tmp4 <@ Primops.staticcall((W256.of_int 1), (W256.of_int 5), (W256.of_int 0), (W256.of_int 192), (W256.of_int 0), (W256.of_int 32));
    success <- tmp4;
    tmp5 <@ Primops.mload((W256.of_int 0));
    ret <- tmp5;
    s <- success;
    r <- ret;
    return (s, r);
    }
  
  (* proc _BODY(): unit = {
    _1 <- (W256.of_int 0);
    } *)
  }.
(* End YulTest *)
