import Mathlib.Tactic

import GS.Extensions.MatrixCalculus
import GS.Extensions.TwoFactorProjection
open GS.MatrixBase



/-!
# Extrinsic geodesic certificates without a covering-space theorem

The conclusions below are actual second
velocity identities and Frobenius normality, not a redefinition of intrinsic
geodesics. The bridge from the derivative image to the tangent bundle of a
smooth embedded orbit remains a separate obligation.

The two coordinate block relations must intersect only on the diagonal.
No such claim is made for the singular general three-factor family.
-/

namespace GS.Extensions


 def OffDiagonalDisjoint (a b : Fin n → ℕ) : Prop :=
  ∀ i j, a i = a j → b i = b j → i = j

 theorem OffDiagonalDisjoint.symm {a b : Fin n → ℕ}
    (h : OffDiagonalDisjoint a b) : OffDiagonalDisjoint b a := by tauto

 theorem frobInner_disjoint_supported_skew {a b : Fin n → ℕ}
    (hab : OffDiagonalDisjoint a b) (A K : Mat n)
    (hA : Supported a A) (hK : Supported b K) (hk : IsSkew K) :
    cFrobInner A K = 0 := by
  
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply mul_eq_zero.mpr
  by_cases ha : a i = a j
  · by_cases hb : b i = b j
    · have hij := hab i j ha hb
      subst j
      right
      have he : K i i = -K i i := congrFun (congrFun hk i) i
      linarith
    · aesop
  · aesop

 def accelerationCore (C K : Mat n) := C*C + (2:ℝ) • (C*K) + K*K


end GS.Extensions
