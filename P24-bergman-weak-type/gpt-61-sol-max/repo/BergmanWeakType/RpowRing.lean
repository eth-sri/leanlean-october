
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic



/-- Reduce positive real-power identities to polynomial identities between logarithms. -/
macro "rpow_ring" : tactic =>
  `(tactic| (
    apply Real.log_injOn_pos <;> try (change (0 : ℝ) < _; positivity)
    simp (disch := positivity) only
      [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Real.log_one]
    ring))
