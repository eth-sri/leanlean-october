module
public import ExtendedHB.CurrentCurve

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Montgomery.MonotoneCurve
open MathCollab.Density

/-- The closed last endpoint remains a uniform bound at every larger real part.
This uses monotonicity of the actual analytic-multiplicity zero count. -/
theorem seven_eighths_right_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 7/8 ≤ σ → ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ ((1086/5537 : ℝ) + ε) := by
  obtain ⟨C, hC, h⟩ :=
    Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8
      (σ := (7/8 : ℝ)) (by norm_num) le_rfl hε
  refine ⟨C, hC, ?_⟩
  intro σ hσ T hT
  have hm : (zetaDensityCount σ T : ℝ) ≤ (zetaDensityCount (7/8) T : ℝ) := by
    exact_mod_cast zetaDensityCount_mono hσ (le_refl T)
  apply hm.trans
  convert h T hT using 1
  norm_num

end Montgomery.MonotoneCurve
