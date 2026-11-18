module

public import GradedNear.Admissible
public import GradedNear.Entry

/-!
# The parabolic autocorrelation tests

The near rows of the leaves use, as detector `f` and as short Gram test `g₁`, the normalized
autocorrelation of the parabola `(γ² - y²)₊` ([HB, §7]; `computations/sieve_near/sieve_inputs.py` in the research repository,
`fnorm`): with `c = 2γ`,
`f(t) = P(t/c)` for `t ≤ c` and `f(t) = 0` for `t > c`, where
`P(u) = (1 - u)³(1 + 3u + u²) = 1 - 5u² + 5u³ - u⁵`, so that `f(0) = 1`.

* `fpar_condition1`: Condition 1 with `x₀ = c` and `B = 10 / c²`;
* `integral_P_cos`: `∫₀¹ P(s) cos(ws) ds = 60 (w cos(w/2) - 2 sin(w/2))² / w⁶` for `w ≠ 0`, which is
  `≥ 0` (the autocorrelation identity `Re F(iy) = (15/(8γ⁵)) (∫₀^γ (γ² - s²) cos(sy) ds)²` in closed
  form);
* `fpar_condition2`: Condition 2, by the criterion `condition2_of_imag_axis`;
* `fpar_anti`, `fpar_pos`: `f` decreases on `[0, ∞)` and is positive on `[0, c)`;
* `laplace_fpar_real`: at a real point, `Re F(x) = c Φ(c x)` with `Φ(u) = ∫₀¹ P(s) e^{-us} ds`;
  `Phi_eq_closed`: the closed form of `Φ(u)` for `u ≠ 0` (five integrations by parts);
  `Phi_sub_taylor`: the Taylor polynomial of `Φ` with its remainder for `|u| ≤ 1`.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Interval

namespace GradedNear

namespace Parabolic

/-- `P(u) = (1 - u)³(1 + 3u + u²) = 1 - 5u² + 5u³ - u⁵`. -/
def P (u : ℝ) : ℝ := 1 - 5 * u ^ 2 + 5 * u ^ 3 - u ^ 5

@[fun_prop] lemma continuous_P : Continuous P := by unfold P; fun_prop

/-- The normalized parabolic autocorrelation of width `c = 2γ`. -/
def fpar (c t : ℝ) : ℝ := if t ≤ c then P (t / c) else 0

/-! ## Condition 2 -/

/-! ## Monotonicity -/

/-! ## The transform at real points -/

end Parabolic

end GradedNear

end
