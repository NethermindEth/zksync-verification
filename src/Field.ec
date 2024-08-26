pragma Goals:printall.

require import AllCore.
require import Int.
require import IntDiv.
require import StdOrder.
require import ZModP.

theory FieldR.
clone include ZModField
  rename "zmod" as "F"
  rename "ZModp" as "Zr".
end FieldR.

theory FieldQ.
clone include ZModField
  rename "zmod" as "F"
  rename "ZModp" as "Zq".
end FieldQ.
  
op (^) (x : FieldR.F) (k : int) = FieldR.exp x k axiomatized by RexpE.
