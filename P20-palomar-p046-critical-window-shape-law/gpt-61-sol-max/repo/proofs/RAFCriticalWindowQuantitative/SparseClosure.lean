
import proofs.RAFCriticalWindowQuantitative.FiniteClosure


namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Concrete RAF.Polymer

variable {M R : Type*}

section
variable [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)

def settledChannels   (C : Finset M)  :=
  S.filter fun r => Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C

/-- Each nonstationary round finishes at least one new channel. -/
abbrev closure_stable_at_channel_count    := by
  let C := revClosureAt Q S
  apply bounded_progress (fun k => C (k+1) = C k) fun k => (settledChannels Q S (C k)).card
  · grind [revClosureAt, settledChannels, revClosureStep]
  · intro n hn
    simp only [C, revClosureAt] at hn ⊢
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · grind [settledChannels, revClosureStep]
    · intro he
      apply hn
      simp only [settledChannels, Finset.ext_iff, Finset.mem_filter] at he
      grind (gen := 16) [revClosureStep, RevEnabledLhs, RevEnabledRhs]
  · intro n
    exact Finset.card_le_card (Finset.filter_subset _ _)
end


variable (N : ℕ) (S : Finset (Reaction N))

theorem finite_iteration_length  (k : ℕ)
    (x : Molecule N) (hx : x ∈ revClosureAt (binaryPolymerCRS N 2) S k) :
    molLength x ≤ 2^(k+1) := by
  induction k generalizing x <;>
    simp_all [revClosureAt, revClosureStep, RevEnabledLhs, RevEnabledRhs,
      binaryPolymerCRS, binaryFood, pow_succ] ;
    grind [reaction_length_add, molLength_reactionLeft,
      molLength_reactionRight, molLength_reactionProduct]

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
abbrev sparse_closure_length 
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure 2 S)  := by
  apply finite_iteration_length N S S.card x
  exact (closureAt_exists_iff _ _ (closure_stable_at_channel_count _ _) x).mp (by simpa using hx)

end RAFCriticalWindowQuantitative
