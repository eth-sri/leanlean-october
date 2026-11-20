module

public import NearlyMinimax.TernarySquareSum
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
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem crude_raw_square_energy_pointwise {d n : ℕ} (Chi η B : ℝ)
    (R : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (x : Fin n → Covariate d) (hcap : ∀ y, |R x y| ≤ Chi^n*η^2*(B+1)) :
    selectedRawSquareEnergy R x ≤ (3*Chi^2)^n*η^4*(B+1)^2 := by
  have he : selectedRawSquareEnergy R x = ∑ y : Fin n → Fin 3, R x y ^ 2 := by
    unfold selectedRawSquareEnergy
    exact Finset.sum_congr (by ext y; simp) (by simp)
  rw [he]
  refine (ternary_sum_sq_le hcap).trans_eq ?_
  rw [mul_pow (3 : ℝ), ← pow_mul]
  simp only [mul_pow, ← pow_mul, Nat.mul_comm 2 n]
  ring

end NearlyMinimax
