module
public import RationalDyadicDifference

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem rational_phase_sum_norm_le_card (r : ℚ) (W : Finset ℝ) :
    ‖∑ t ∈ W, phase r t‖ ≤ W.card := by
  have hp (t : ℝ) : ‖phase r t‖ = 1 := by
    rw [← exponentialPhase_log, exponentialPhase_norm]
  exact (norm_sum_le _ _).trans_eq (by simp only [hp, sum_const, nsmul_eq_mul, mul_one])




