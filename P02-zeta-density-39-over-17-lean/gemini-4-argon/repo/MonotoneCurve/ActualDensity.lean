module
public import LaterPairs.NativeSharpRows78

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Montgomery.MonotoneCurve
open MathCollab.Density

theorem seven_eighths_right_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 7/8 ≤ σ → ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C * T ^ ((1086/5537 : ℝ) + ε) := by
  obtain ⟨C, hC, h⟩ :=
    Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8
      (σ := (7/8 : ℝ)) (by norm_num) le_rfl hε
  refine ⟨C, hC, fun σ hσ T hT => ?_⟩
  have hm : (zetaDensityCount σ T : ℝ) ≤ (zetaDensityCount (7/8) T : ℝ) := by
    exact_mod_cast zetaDensityCount_mono hσ (le_refl T)
  refine hm.trans ?_
  convert h T hT using 1
  norm_num

