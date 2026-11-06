module
public import RationalDyadicShortRange

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Montgomery.RationalMoment

theorem adjacent_rpow_nat {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x^a)^n = x^(a*(n:ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]




