module
public import DensityStrip.Prefix
public import LaterPairs.Native.ParabolaBilinearLocalization.Part03

@[expose] public section

open Complex
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Bourgain’s logarithmic-phase bound implies the all-height Weyl input. -/
theorem actual_zeta_weyl_input {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η₀) := by
  obtain ⟨C,hC,h⟩ := DensityStrip.pair_growth TaoTrudgianYang2025.exponentPair_bourgain
    (e:=1/200) (b:=1/2) (by norm_num) le_rfl (by norm_num) (by norm_num)
  push_cast at h
  refine ⟨C,hC,fun t => (h t).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by linarith [abs_nonneg t]) (by linarith)) hC.le

end MathCollab.Density
