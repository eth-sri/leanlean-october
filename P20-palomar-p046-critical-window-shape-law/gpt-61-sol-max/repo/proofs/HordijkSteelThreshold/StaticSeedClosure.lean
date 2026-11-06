
import proofs.HordijkSteelThreshold.TemporaryReactionClosure




namespace HordijkSteelThreshold
open RAF.Polymer RAF.Concrete

/-- Induction over actual reversible generation, including both reaction directions. -/
theorem temporaryReactionClosure_induction {N L : ℕ} (S : _)
    (P : Molecule N → Prop)
    (hfood : ∀ x, molLength x ≤ L → P x)
    (hlig : ∀ r ∈ S, P (reactionLeft r) → P (reactionRight r) → P (reactionProduct r))
    (hcleave : ∀ r ∈ S, P (reactionProduct r) → P (reactionLeft r) ∧ P (reactionRight r))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L S) : P x := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  clear hx
  induction k generalizing x <;>
    simp_all [revClosureAt, revClosureStep, RevEnabledLhs, RevEnabledRhs,
      binaryPolymerCRS, binaryFood]; grind



end HordijkSteelThreshold
