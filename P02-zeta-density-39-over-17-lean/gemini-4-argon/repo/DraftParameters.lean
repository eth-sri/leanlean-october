module
public import Mathlib

@[expose] public section

/- These are parameter theorems only. No zero-density result is asserted
from the newer rational moment or trace estimates in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Montgomery.DraftParameters

/-- Complete quadratic length-window budgets from the two lower bounds on a.
The equality p=3a(1-s) is retained in the statement. -/
theorem quadratic_window {s a x : ℝ}
    (hs : 3/4 < s) (hs' : s < 1) (_ha : 0 ≤ a) (ha' : a ≤ 2/3)
    (h₁ : 2 ≤ a*(3*s+1)) (h₂ : 1 ≤ a*(11*s-7))
    (hx : a ≤ x) (hx' : x ≤ 3*a/2) :
    let p := 3*a*(1-s)
    let ell := p+(2*s-1)*x
    x ≤ ell ∧ ell ≤ 1 ∧
    1 ≤ (3/2)*p+(6*s-4)*x ∧
    (1/4) ≤ (5/12)*p+(4*s-3)*x := by
  dsimp
  have ht : 0 ≤ (1-s)*(3*a-2*x) := mul_nonneg (by linarith) (by linarith)
  have hu : 0 ≤ (2*s-1)*(3*a/2-x) := mul_nonneg (by linarith) (by linarith)
  have hv : 0 ≤ (6*s-4)*(x-a) := mul_nonneg (by linarith) (by linarith)
  have hw : 0 ≤ (4*s-3)*(x-a) := mul_nonneg (by linarith) (by linarith)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

