
import proofs.HordijkSteelThreshold.TemporaryReactionClosure
import proofs.HordijkSteelThreshold.PeelingHistory




namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Polymer RAF.Concrete

def fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R)  := revClosureAt Q S (Fintype.card M)

/-- A finite executable evaluator, using the literal source's closure iteration. -/
def computedClosure (N L : ℕ) (S : Finset (Reaction N))  :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

variable {M R : Type*}

section
variable [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)

theorem closureAt_eq_of_stable   {b k : ℕ}
    (h : revClosureAt Q S (b+1) = revClosureAt Q S b) (hk : b ≤ k) :
    revClosureAt Q S k = revClosureAt Q S b := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    grind [revClosureAt, revClosureStep]

theorem closureAt_exists_iff   {b : ℕ}
    (h : revClosureAt Q S (b+1) = revClosureAt Q S b) (x : M) :
    (∃ k, x ∈ revClosureAt Q S k) ↔ x ∈ revClosureAt Q S b := by
  constructor
  · rintro ⟨k,hk⟩
    by_cases hb : k ≤ b
    · exact revClosureAt_mono_stage Q S hb hk
    · grind [closureAt_eq_of_stable]
  · exact fun hx => ⟨b,hx⟩
end


abbrev closure_stable_at_card  [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (Fintype.card M+1) = revClosureAt Q S (Fintype.card M) := by
  let C := revClosureAt Q S
  apply bounded_progress (fun k => C (k+1) = C k) fun k => (C k).card
  · grind [revClosureAt]
  · intro n hn
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨revClosureAt_mono_stage Q S (Nat.le_succ n), Ne.symm hn⟩)
  · intro n
    exact Finset.card_le_univ _

/-- Exact semantics: the executable finite iteration equals the existing closure. -/
theorem computedClosure_eq (N L : ℕ) (S : _) :
    computedClosure N L S = temporaryReactionClosure L S := by
  ext x
  simp
  exact (closureAt_exists_iff _ _ (closure_stable_at_card _ _) x).symm

end RAFCriticalWindowQuantitative

namespace HordijkSteelThreshold
open RAF.Polymer RAF.Concrete RAFCriticalWindowQuantitative
variable {N L : ℕ} (S : Finset (Reaction N))

theorem temporaryReactionClosure_stable :
    revClosureStep (binaryPolymerCRS N L) S (temporaryReactionClosure L S) =
      temporaryReactionClosure L S := by
  rw [← computedClosure_eq]
  exact closure_stable_at_card _ _
theorem temporaryReactionClosure_rules (r : Reaction N) (hr : r ∈ S) :
    (reactionLeft r ∈ temporaryReactionClosure L S →
      reactionRight r ∈ temporaryReactionClosure L S →
      reactionProduct r ∈ temporaryReactionClosure L S) ∧
    (reactionProduct r ∈ temporaryReactionClosure L S →
      reactionLeft r ∈ temporaryReactionClosure L S ∧
      reactionRight r ∈ temporaryReactionClosure L S) := by
  have hs := temporaryReactionClosure_stable (L := L) S
  simp only [revClosureStep, RevEnabledLhs, RevEnabledRhs, binaryPolymerCRS] at hs
  grind

end HordijkSteelThreshold
