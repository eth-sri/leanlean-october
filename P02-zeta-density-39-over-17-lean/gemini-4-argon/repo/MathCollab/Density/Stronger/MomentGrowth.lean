module
public import MathCollab.Density.Stronger.WeightedTwelfth
public import MathCollab.Density.WeylInput
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Filter MeasureTheory Set Complex Real
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger

/-- Uniform slab growth with the constant absorbed before the ordinate.
This uses the already proved actual-zeta Weyl estimate. -/
theorem zetaMomentCriticalNorm_eventually_lt_slab_power {η : ℝ} (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop, ∀ t : ℝ, |t| ≤ 2*H →
      zetaMomentCriticalNorm t < H^(1/6+η) := by
  obtain ⟨C,hC,hW⟩ := actual_zeta_weyl_input (by linarith : 0 < η/2)
  let K : ℝ := C*(3 : ℝ)^(1/6+η/2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < η/2)).eventually_gt_atTop K] with H hH hK
  intro t ht
  have hHp : 0 < H := by linarith
  have hW' : zetaMomentCriticalNorm t ≤ C*(1+|t|)^(1/6+η/2) := by
    simpa [zetaMomentCriticalNorm] using hW t
  calc
    _ ≤ C*(1+|t|)^(1/6+η/2) := hW'
    _ ≤ C*(3*H)^(1/6+η/2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)) hC.le
    _ = K*H^(1/6+η/2) := by rw [Real.mul_rpow (by norm_num) hHp.le]; dsimp [K]; ring
    _ < H^(η/2)*H^(1/6+η/2) := mul_lt_mul_of_pos_right hK (Real.rpow_pos_of_pos hHp _)
    _ = H^(1/6+η) := by rw [← Real.rpow_add hHp]; congr 1; ring


