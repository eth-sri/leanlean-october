module

public import proofs.RAFCriticalWindowQuantitative.FiniteClosure

public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Concrete RAF.Polymer

/-- Each nonstationary round finishes at least one new channel. -/
theorem sparse_closure_sub {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (k : ℕ) : revClosureAt Q S k ⊆ revClosureAt Q S S.card :=
  revClosureAt_sub Q S (fun C => (S.filter fun r => Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C).card) _
    (fun _ => Finset.card_filter_le _ _) (fun C hg => by
      have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
      obtain ⟨x,hx,hnot⟩ := Finset.not_subset.mp fun hh => hg $ hh.antisymm hold
      obtain ⟨r,hr,hxr⟩ := Finset.mem_biUnion.mp $ (Finset.mem_union.mp hx).resolve_left hnot
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset
        (Finset.monotone_filter_right _ ?_)).2 ⟨r, ?_, ?_⟩) <;>
        grind [revClosureStep, RevEnabledLhs, RevEnabledRhs]) k

variable {N : ℕ}

/-- A sparse set of open channels cannot generate an arbitrarily long molecule. -/
theorem closure_length  {R : Type*} (Q : ReversibleCRS (Molecule N) R)
    (h0 : ∀ x ∈ Q.food, molLength x ≤ 2)
    (hQ : ∀ r B, ((∀ y ∈ Q.lhs r, molLength y ≤ B) → ∀ y ∈ Q.rhs r, molLength y ≤ 2*B) ∧
      ((∀ y ∈ Q.rhs r, molLength y ≤ B) → ∀ y ∈ Q.lhs r, molLength y ≤ 2*B))
    (S : Finset R) (k : ℕ) (x : Molecule N) (hx : x ∈ revClosureAt Q S k) :
    molLength x ≤ 2^(S.card+1) := by
  have (k x) (hx : x ∈ revClosureAt Q S k) : molLength x ≤ 2^(k+1) := by
    induction k generalizing x with
    | zero => aesop
    | succ k ih =>
      simp only [revClosureAt, revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx
      rw [pow_succ']
      rcases hx with hx | ⟨r, -, hx | hx⟩
      · grind
      all_goals split_ifs at hx with h
      · exact (hQ r _).1 (fun y hy => ih y $ h hy) x hx
      · simp_all
      · exact (hQ r _).2 (fun y hy => ih y $ h hy) x hx
      simp_all
  exact this _ x $ sparse_closure_sub Q S k hx

theorem split_closure_length  (S : Finset $ Reaction N) (x : Molecule N)
    (hx : x ∈ temporaryReactionClosure 2 S) : molLength x ≤ 2^(S.card+1) := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure _ _).1 hx
  refine closure_length _ (by simp [binaryPolymerCRS, binaryFood]) (fun r B => ?_) S k x hk
  have := reaction_length_add r
  simp only [binaryPolymerCRS, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]
  omega

end RAFCriticalWindowQuantitative
