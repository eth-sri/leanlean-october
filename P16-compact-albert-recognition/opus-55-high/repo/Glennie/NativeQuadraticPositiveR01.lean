/- Native U positivity from coordinate identities, transport, and cone closure.
   No associative octonionic matrix multiplication is used. -/
module
public import Glennie.NativeSquareConeR01


@[expose] public section
namespace Glennie.NativeQuadraticPositiveR01

@[simp] theorem octConj_zero_local : octConj (0 : Octonion) = 0 := by
  simp [octConj]

@[simp] theorem octMul_zero_left_local (x : Octonion) :
    octMul 0 x = 0 := by
  simp [octMul]

@[simp] theorem octMul_zero_right_local (x : Octonion) :
    octMul x 0 = 0 := by
  simp [octMul]

end Glennie.NativeQuadraticPositiveR01
