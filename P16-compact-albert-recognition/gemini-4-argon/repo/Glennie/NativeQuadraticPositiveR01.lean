/- Native U positivity from coordinate identities, transport, and cone closure.
   No associative octonionic matrix multiplication is used. -/
module
public import Glennie.NativeSquareConeR01

set_option linter.privateModule false

@[expose] public section
namespace Glennie.NativeQuadraticPositiveR01
open Glennie
noncomputable section
set_option autoImplicit false

@[simp] private theorem octConj_zero_local : octConj (0 : Octonion) = 0 := by
  simp [octConj]

@[simp] private theorem octMul_zero_left_local (x : Octonion) :
    octMul 0 x = 0 := by
  simp [octMul]

@[simp] private theorem octMul_zero_right_local (x : Octonion) :
    octMul x 0 = 0 := by
  simp [octMul]

end
end Glennie.NativeQuadraticPositiveR01
