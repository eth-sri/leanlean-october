module
public import GuthMaynard.Improvement.CubicModeCount

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

/-- Order fixed after eta and before all scales and densities. -/
theorem choose_radial_discard_order {η : ℝ} (hη : 0 < η) :
    ∃ n : ℕ, ∀ T : ℝ, 1 ≤ T →
      T^(6+3*η)/(T^η)^n ≤ T^(-100:ℝ) := by
  let n := ⌈(106+3*η)/η⌉₊
  have hn : 106+3*η ≤ (n:ℝ)*η := (div_le_iff₀ hη).mp (Nat.le_ceil _)
  refine ⟨n,?_⟩
  intro T hT
  have hTp : 0 < T := by linarith
  rw [← Real.rpow_natCast (T^η) n, ← Real.rpow_mul hTp.le, ← Real.rpow_sub hTp]
  exact Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)

end GuthMaynard.Improvement
