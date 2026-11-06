module

public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-!
# Loewner polarization

This module turns two-sided Loewner bounds into the sharp polarized quadratic bound.
-/

 public section

open scoped BigOperators MatrixOrder
open Matrix

namespace HypoellipticAleksandrov

variable {d : ℕ}

private theorem matrix_isSymm_of_loewner_lower  {lam : ℝ} {A : PDE.Mat d}
    (hlower : lam • (1 : PDE.Mat d) ≤ A) : A.IsSymm := by

  refine Matrix.IsSymm.ext ?_
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  ·

    simpa only [Matrix.sub_apply, Matrix.smul_apply, one_apply, (Ne.symm hij), ite_false, smul_zero, sub_zero,
      star_trivial, hij] using ((Matrix.le_iff.mp hlower).isHermitian.apply i j)

private theorem vecDot_mulVec_comm_of_isSymm  {A : PDE.Mat d}
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

private theorem vecDot_mulVec_upper_of_loewner  {Lam : ℝ} {A : PDE.Mat d}
    (hupper : A ≤ Lam • (1 : PDE.Mat d)) (W : PDE.Vec d) :
    PDE.vecDot W (A *ᵥ W) ≤ Lam * PDE.vecNormSq W := by

  have hquad := vecDot_mulVec_lower_of_loewner (show (-Lam) • (1 : PDE.Mat d) ≤ -A by
      simpa only [neg_smul] using neg_le_neg hupper) W
  have hrewrite : PDE.vecDot W ((-A) *ᵥ W) = -PDE.vecDot W (A *ᵥ W) := by
    simp only [neg_mulVec, PDE.vecDot, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib]
  simp_all

/-- Two-sided Loewner bounds control the polarized coordinate form with no
sign assumptions on either bound. -/
theorem vecDot_add_mulVec_sub_lower_of_loewner
     {lam Lam : ℝ} {A : PDE.Mat d}
    (hlower : lam • (1 : PDE.Mat d) ≤ A)
    (hupper : A ≤ Lam • (1 : PDE.Mat d))
    (G W : PDE.Vec d) :
    lam * PDE.vecNormSq G - Lam * PDE.vecNormSq W ≤
      PDE.vecDot (G + W) (A *ᵥ (G - W)) := by



  have hcross := vecDot_mulVec_comm_of_isSymm (matrix_isSymm_of_loewner_lower hlower) G W
  calc
    lam * PDE.vecNormSq G - Lam * PDE.vecNormSq W ≤
        PDE.vecDot G (A *ᵥ G) - PDE.vecDot W (A *ᵥ W) := sub_le_sub (vecDot_mulVec_lower_of_loewner hlower G) (vecDot_mulVec_upper_of_loewner hupper W)
    _ = PDE.vecDot (G + W) (A *ᵥ (G - W)) := by
      rw [Matrix.mulVec_sub]
      change (∑ i, G i * (A *ᵥ G) i) - ∑ i, W i * (A *ᵥ W) i =
        ∑ i, (G i + W i) * ((A *ᵥ G) i - (A *ᵥ W) i)
      change (∑ i, G i * (A *ᵥ W) i) = ∑ i, W i * (A *ᵥ G) i at hcross
      simp only [add_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      linarith

end HypoellipticAleksandrov
