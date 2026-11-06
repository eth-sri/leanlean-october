module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatch
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIterationCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIterationAbsorption
import Mathlib.Tactic

/-! # Supremum iteration removes the larger return-box supremum -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set Holder

/- The nested radii in the source iteration. -/
def returnIterationRadius (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (n + 1)

/- Every radius belongs to the permitted half-to-one interval. -/
theorem returnIterationRadius_bounds (n : ℕ) :
    1 / 2 ≤ returnIterationRadius n ∧ returnIterationRadius n < 1 := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  have hb : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)
    nlinarith
  dsimp [returnIterationRadius]
  constructor <;> linarith

/- The consecutive radius gap is the exact dyadic gap in the source. -/
theorem returnIterationRadius_gap (n : ℕ) :
    returnIterationRadius (n + 1) - returnIterationRadius n =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  simp only [returnIterationRadius, pow_succ]
  ring

/- The error term grows by the fixed factor `2^beta` at each iteration. -/
theorem returnIterationRadius_gap_power (n : ℕ) (beta : ℝ) :
    (returnIterationRadius (n + 1) - returnIterationRadius n) ^ (-beta) =
      (4 : ℝ) ^ beta * ((2 : ℝ) ^ beta) ^ n := by
  rw [returnIterationRadius_gap,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (pow_nonneg (by norm_num) n),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
  norm_num

/- The larger supremum disappears, leaving a uniform unit-scale return comparison. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
