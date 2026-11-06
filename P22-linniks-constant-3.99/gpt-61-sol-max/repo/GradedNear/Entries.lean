import GradedNear.Tactics
import GradedNear.SieveError

import GradedNear.Gram

/-!
# Bounds for the Gram entries

* principal entries (same character) from [X, Lemma 3.1]:
  `𝓛⁻¹ Re primeSum(1, g, s) ≤ Re G((s - 1)𝓛) + ε`;
* non-principal entries (distinct characters) from [X, Lemma 3.2], when no zero of the
  quotient `L`-function in the local disc lies to the right of `s`: `≤ g(0)/6 + ε`.
-/

namespace GradedNear

/-- Eventually `√(log log q) ≥ K` and `q ≥ 2`. -/
lemma eventually_loglog_ge (K : ℝ) : ∀ᶠ q : ℕ in Filter.atTop,
    K ≤ Real.sqrt (Real.log (Real.log q)) ∧ 2 ≤ q := by
  exact
    ((Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_log_nat_atTop)).eventually_ge_atTop K).and
      (Filter.eventually_ge_atTop (2 : ℕ))

end GradedNear
