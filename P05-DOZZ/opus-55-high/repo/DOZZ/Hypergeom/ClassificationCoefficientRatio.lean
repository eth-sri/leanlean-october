/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationAssembly
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients

/-! The nondegenerate scalar normalization of the real Gauss classification. -/

@[expose] public section

namespace DOZZ.Proofs

/-- On the nonzero `K₂` locus, the unique diagonal classification normalizes to the coefficient
ratio `gaussCoefficientRatio` of [KRV, (Fundrelation)]. -/
theorem real_gauss_solution_coefficient_ratio
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hK₂ : gaussK₂ a b c ≠ 0) (T : ℂ → ℝ)
    (hT : IsRealGaussSolution a b c T) :
    ∃! coeff : ℝ, ∀ z ∈ gaussCutPlane,
      T z = coeff * (‖gaussFMinus H a b c z‖ ^ 2 +
        gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2) := by
  obtain ⟨v, hv, hv_unique⟩ :=
    real_gauss_solution_classification hH a b c hc hδ T hT
  have hratio := gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero a b c hK₂
  have hratio' : gaussK₁ a b c +
      gaussCoefficientRatio a b c * gaussK₂ a b c = 0 := by
    linarith
  have hv₂ : v.2 = gaussCoefficientRatio a b c * v.1 := by
    grind
  refine ⟨v.1, ?_, ?_⟩
  · grind
  · intro coeff hcoeff
    have hconstraint : gaussK₁ a b c * coeff +
        gaussK₂ a b c * (gaussCoefficientRatio a b c * coeff) = 0 := by
      grind
    have hrepresentation : ∀ z ∈ gaussCutPlane,
        T z = coeff * ‖gaussFMinus H a b c z‖ ^ 2 +
          (gaussCoefficientRatio a b c * coeff) *
            ‖gaussFPlus H a b c z‖ ^ 2 := by
      grind
    have hv_eq := hv_unique (coeff, gaussCoefficientRatio a b c * coeff)
      ⟨hconstraint, hrepresentation⟩
    grind

end DOZZ.Proofs
