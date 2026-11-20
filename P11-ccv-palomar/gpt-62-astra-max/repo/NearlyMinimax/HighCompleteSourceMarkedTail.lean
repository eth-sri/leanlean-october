module

public import NearlyMinimax.HighCompleteSourceSpatialTail

@[expose] public section

/-! Large-count factorial energy of the genuine canonical complete source
in the original periodic-frame field. All source field guards are derived;
the fixed tail constant precedes degree, count, history and spatial grid. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem crude_raw_square_energy_pointwise {d n : ℕ} (Chi η B : ℝ)
    (hChi : 0 ≤ Chi) (hB : 0 ≤ B)
    (R : (DesignSample d n) → (TernaryVector n) → ℝ)
    (hcap : ∀ x y, |R x y| ≤ Chi^n*η^2*(B+1)) (x : DesignSample d n) :
    selectedRawSquareEnergy R x ≤ (3*Chi^2)^n*η^4*(B+1)^2 := by
  have hp (y) : R x y ^ 2 ≤ Chi^(2*n)*η^4*(B+1)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Chi^n*η^2*(B+1))).mpr (hcap x y)
    simp at hh
    convert hh using 1 <;> (try rw [mul_pow,mul_pow,←pow_mul]) <;> ring
  have he : selectedRawSquareEnergy R x = ∑ y : TernaryVector n, R x y ^ 2 := by
    unfold selectedRawSquareEnergy
    apply Finset.sum_congr (by ext y; simp)
    intro y _
    rfl
  calc
    _ = _ := he
    _ ≤ _ :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = _ := by
      simp
      ring

end NearlyMinimax
