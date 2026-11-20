module

public import HypoellipticAleksandrov.Coefficients.Ellipticity
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
import HypoellipticAleksandrov.Parabolic.ResolventBarrier

/-!
# Loewner polarization

This module turns two-sided Loewner bounds into the sharp polarized quadratic bound.
-/

@[expose] public section

open scoped BigOperators MatrixOrder
open Matrix

namespace HypoellipticAleksandrov

private theorem vecDot_mulVec_comm_of_isSymm {d : ℕ} {A : PDE.Mat d}
    (hA : A.IsSymm) (G W : PDE.Vec d) :
    PDE.vecDot G (A *ᵥ W) = PDE.vecDot W (A *ᵥ G) := by
  classical
  unfold PDE.vecDot Matrix.mulVec
  simp only [dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA.apply]
  ring

/-- Two-sided Loewner bounds control the polarized coordinate form with no
sign assumptions on either bound. -/
theorem vecDot_add_mulVec_sub_lower_of_loewner
    {d : ℕ} {lam Lam : ℝ} {A : PDE.Mat d}
    (hlower : lam • (1 : PDE.Mat d) ≤ A)
    (hupper : A ≤ Lam • (1 : PDE.Mat d))
    (G W : PDE.Vec d) :
    lam * PDE.vecNormSq G - Lam * PDE.vecNormSq W ≤
      PDE.vecDot (G + W) (A *ᵥ (G - W)) := by
  have hG := vecDot_mulVec_lower_of_loewner hlower G
  have hW := _root_.HypoellipticAleksandrov.Parabolic.vecDot_mulVec_le_of_loewner_upper hupper W
  have hcross := vecDot_mulVec_comm_of_isSymm (_root_.HypoellipticAleksandrov.Parabolic.isSymm_of_lower_ellipticity hlower) G W
  calc
    lam * PDE.vecNormSq G - Lam * PDE.vecNormSq W ≤
        PDE.vecDot G (A *ᵥ G) - PDE.vecDot W (A *ᵥ W) := sub_le_sub hG hW
    _ = PDE.vecDot (G + W) (A *ᵥ (G - W)) := by
      rw [Matrix.mulVec_sub]
      change (∑ i, G i * (A *ᵥ G) i) - ∑ i, W i * (A *ᵥ W) i =
        ∑ i, (G i + W i) * ((A *ᵥ G) i - (A *ᵥ W) i)
      change (∑ i, G i * (A *ᵥ W) i) = ∑ i, W i * (A *ᵥ G) i at hcross
      simp only [add_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      linarith

end HypoellipticAleksandrov
