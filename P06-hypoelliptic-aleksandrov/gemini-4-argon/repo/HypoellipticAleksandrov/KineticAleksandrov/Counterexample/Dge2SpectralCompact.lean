module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Spectral
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Positivity

/-!
# Compactness choices for the Appendix C spectral weights

These are elementary compactness lemmas. Their application to the actual cutoff
Hessian must establish all sign hypotheses from its derivatives.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- A single finite negative weight makes the trace numerator positive on a compact set. -/
theorem exists_positive_bounds_on_compact {X : Type*} [TopologicalSpace X]
    (K ) (hK : IsCompact K) (w : X → ℝ) (hw : ContinuousOn w K)
    (hpos : ∀ x ∈ K, 0 < w x) :
    ∃ lower upper : ℝ, 0 < lower ∧ lower ≤ upper ∧
      ∀ x ∈ K, lower ≤ w x ∧ w x ≤ upper := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hw
    obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hw
    refine ⟨w a, w b, hpos a ha, hmin hb, ?_⟩
    intro x hx
    exact ⟨hmin hx, hmax hx⟩
  · refine ⟨1, 1, zero_lt_one, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
