module

public import RequestProject.LocalConformalRegularPrincipal
public import RequestProject.CorrectedKernelSymm
public import RequestProject.ConormalNormalization
public import RequestProject.SobolevMultiplier

/-!
# The Fourier operator assembled from the genuine regular Neumann map

The definition uses the actual regular weak resolvent and the actual
corrected-kernel matrix. Its compact principal remainder is proved here.
Identification with the physical periodic boundary expression is a
separate mathematical statement, not an assumption of this file.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open Set Metric

def normalizedPeriodicRegularOperator 
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (E₀ E : ℝ)
    W
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    L2Z →L[ℂ] L2Z :=
  (2 : ℂ) • (normalizedNeumannRegular Q E₀ E - normalizedInverseAbsOperator) +
    principalNormalized + hsMatrixOp (correctedRemainderMatrix W 0 0) hbase

section PhysicalCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)


local notation "Φ0" => localConformalDiskHalfTrace hR F hFs hL
include hb hhol hinj hC e he hsource hes in
theorem localConformal_normalizedPeriodicRegular_sub_four_posProj_compact
    {E₀ E : ℝ} (hE₀ : 0 ≤ E₀)
    (hunit : IsUnit (h1ComplementForm (F '' ball 0 1) E₀ E))
    W
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2) :
    IsCompactOperator (normalizedPeriodicRegularOperator
      (localConformalDiskHalfTrace hR F hFs hL) E₀ E W hbase - (4 : ℂ) • posProj) := by
  exact (by
    rw [show normalizedPeriodicRegularOperator (Φ0) E₀ E W hbase - (4 : ℂ) • posProj = (2 : ℂ) • (normalizedNeumannRegular (Φ0) E₀ E - normalizedInverseAbsOperator) + (principalNormalized - (4 : ℂ) • posProj) + hsMatrixOp (correctedRemainderMatrix W 0 0) hbase by
      unfold normalizedPeriodicRegularOperator
      abel]
    exact (((show IsCompactOperator (normalizedNeumannRegular (Φ0) E₀ E - normalizedInverseAbsOperator) by
      have heq : normalizedNeumannRegular (Φ0) E₀ E - normalizedInverseAbsOperator =
          normalizedNeumannRegular (Φ0) E₀ E - 1 - (normalizedInverseAbsOperator - 1) := by abel
      rw [heq]
      exact (isCompactOperator_localConformal_normalizedNeumannRegular_sub_one hR F hFs hb hL hhol hinj hC e he hsource hes hE₀ hunit).sub (by
        rw [show normalizedInverseAbsOperator - (1 : L2Z →L[ℂ] L2Z) = (sobolevSmoothing 1 zero_le_one).comp normalizedInverseAbsOperator - zeroModeProjection by
          apply ContinuousLinearMap.ext
          intro b
          apply lp.ext
          funext n
          simp [sobolevSmoothing]
          by_cases hn : n = 0
          · subst n
            simp [normalizedInverseAbsSymbol]
          · simp [if_neg hn]
            calc
              _ = (normalizedInverseAbsSymbol n - 1) * b n := by ring
              _ = _ := by rw [(show normalizedInverseAbsSymbol n - 1 = (sobWeight n ^ (-(1 : ℝ)) : ℝ) * normalizedInverseAbsSymbol n by
                have hr : sobWeight n / |(n : ℝ)| - 1 =
                    sobWeight n ^ (-(1 : ℝ)) * (sobWeight n / |(n : ℝ)|) := by
                  rw [Real.rpow_neg (sobWeight_pos n).le, Real.rpow_one]
                  field_simp [(sobWeight_pos n).ne', abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn)]
                  simp only [sobWeight]
                  ring
                simp only [normalizedInverseAbsSymbol, if_neg hn]
                exact_mod_cast hr)]; ring]
        exact ((isCompactOperator_sobolevSmoothing zero_lt_one).comp_clm
          normalizedInverseAbsOperator).sub isCompactOperator_zeroModeProjection)).smul (2 : ℂ)).add principal_normalized_sub_four_posProj_compact).add
      (isCompactOperator_hsMatrixOp _ hbase))

end PhysicalCoordinates

end PolyaNeumann

end
