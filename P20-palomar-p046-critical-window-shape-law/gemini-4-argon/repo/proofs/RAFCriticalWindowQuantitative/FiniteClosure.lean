module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete

def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

theorem revClosureAt_subset_of_stable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {K : ℕ}
    (h : revClosureStep Q S (revClosureAt Q S K) = revClosureAt Q S K) (k : ℕ) :
    revClosureAt Q S k ⊆ revClosureAt Q S K := by
  induction k with
  | zero => exact revClosureAt_mono_stage Q S (Nat.zero_le _)
  | succ k ih => exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans (Finset.subset_of_eq h)

theorem filter_revClosureAt_eq_of_stable {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {K : ℕ}
    (h : revClosureAt Q S (K + 1) = revClosureAt Q S K) :
    Finset.univ.filter (fun x => ∃ k, x ∈ revClosureAt Q S k) = revClosureAt Q S K :=
  Finset.Subset.antisymm
    (fun _ hx => let ⟨k, hk⟩ := (Finset.mem_filter.mp hx).2; revClosureAt_subset_of_stable Q S h k hk)
    (fun _ hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, K, hx⟩)

theorem closure_growth_or_stable {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (k : ℕ) :
    k ≤ (revClosureAt Q S k).card ∨ revClosureAt Q S (k+1) = revClosureAt Q S k := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
    · exact Or.inr (by change revClosureStep Q S (revClosureAt Q S (k+1)) = _; rw [he]; exact he)
    · exact Or.inl <| ih.resolve_right he |>.trans_lt <| Finset.card_lt_card <|
        Finset.ssubset_iff_subset_ne.mpr ⟨revClosureAt_mono_stage Q S (Nat.le_succ k), Ne.symm he⟩

theorem closure_stable_at_card {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (Fintype.card M+1) = revClosureAt Q S (Fintype.card M) := by
  rcases closure_growth_or_stable Q S (Fintype.card M) with hg | he
  ·refine Finset.Subset.antisymm ?_ (revClosureAt_mono_stage Q S (Nat.le_succ _))
   rw [Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hg)]
   exact Finset.subset_univ _
  · exact he

theorem computedClosure_eq (N L : ℕ) (S : Finset (Reaction N)) :
    computedClosure N L S = temporaryReactionClosure L S :=
  (filter_revClosureAt_eq_of_stable (binaryPolymerCRS N L) S (closure_stable_at_card _ S)).symm

end RAFCriticalWindowQuantitative
