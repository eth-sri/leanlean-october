module

public import GradedNear.Gram

/-! # Eventual bounds on `log log q` -/

@[expose] public section

noncomputable section

namespace GradedNear

/-- Eventually `√(log log q) ≥ K` and `log log q ≥ K`. -/
lemma eventually_loglog_ge (K : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    K ≤ Real.sqrt (Real.log (Real.log q)) ∧ K ≤ Real.log (Real.log q) ∧ 2 ≤ q := by
  have h := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact Filter.eventually_atTop.1 (((Real.tendsto_sqrt_atTop.comp h).eventually_ge_atTop K).and
    ((h.eventually_ge_atTop K).and (Filter.eventually_ge_atTop 2)))

end GradedNear
