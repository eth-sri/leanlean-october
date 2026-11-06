module

public import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source

def fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M := revClosureAt Q S (Fintype.card M)

inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

theorem productive_extension {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S T : Finset R) (x : M)
    (hx : x ∈ fullClosure Q S) (hnot : x ∉ fullClosure Q T) :
    ∃ r ∈ S, r ∉ T ∧ revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T := by
  let C := fullClosure Q T
  have hg : revClosureStep Q S C ≠ C := fun he => hnot <| by
    have hall (k : ℕ) : revClosureAt Q S k ⊆ C := by
      induction k with
      | zero => exact revClosureAt_mono_stage Q T (Nat.zero_le _)
      | succ k ih => exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans (Finset.subset_of_eq he)
    exact hall _ hx
  obtain ⟨r, hr, hgrow⟩ : ∃ r ∈ S, revClosureStep Q {r} C ≠ C := by
    by_contra! h; refine hg (Finset.Subset.antisymm (fun y hy => ?_) Finset.subset_union_left)
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hy
    · obtain ⟨r, hr, hy⟩ := Finset.mem_biUnion.mp hy
      exact h r hr ▸ Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_singleton_self _, hy⟩)
  exact ⟨r, hr, fun hrT => hgrow <| Finset.Subset.antisymm
    ((revClosureStep_mono Q (Finset.singleton_subset_iff.mpr hrT) Finset.Subset.rfl).trans
      (Finset.subset_of_eq (closure_stable_at_card Q T))) Finset.subset_union_left, hgrow⟩

theorem long_target_productive_history {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (length : M → ℕ)
    (hbound : ∀ T x, x ∈ fullClosure Q T → length x ≤ 2^(T.card+1))
    (S : Finset R) (k : ℕ) (x : M) (hx : x ∈ fullClosure Q S) (hlen : 2^(k+1) < length x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S := by
  induction k with
  | zero => exact ⟨∅, .nil, Finset.card_empty, Finset.empty_subset _⟩
  | succ k ih =>
    obtain ⟨T, hT, hcard, hTS⟩ := ih ((Nat.pow_le_pow_right (by omega) (by omega)).trans_lt hlen)
    obtain ⟨r, hr, hrT, hgrow⟩ := productive_extension Q S T x hx fun hh => by
      have := hbound T x hh; rw [hcard] at this; omega
    exact ⟨insert r T, .step hT hr hrT hgrow,
      by rw [Finset.card_insert_of_notMem hrT, hcard], Finset.insert_subset hr hTS⟩

theorem split_long_target_history (N k : ℕ) (S : Finset (Reaction N)) (x : Molecule N)
    (hx : x ∈ temporaryReactionClosure 2 S) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S :=
  long_target_productive_history _ molLength
    (fun T y hy => sparse_closure_length N T y (by rwa [← computedClosure_eq]))
    S k x (by rwa [← computedClosure_eq] at hx) hlen

theorem quotient_long_target_history (N k : ℕ) (S : Finset (RepositoryChannel N)) (x : Molecule N)
    (hx : x ∈ quotientClosure N 2 S) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S := by
  have he (T : Finset (RepositoryChannel N)) : quotientClosure N 2 T = fullClosure (repositoryCRS N 2) T :=
    filter_revClosureAt_eq_of_stable (repositoryCRS N 2) T (closure_stable_at_card _ T)
  exact long_target_productive_history _ molLength
    (fun T y hy => quotient_sparse_closure_length N T y (he T ▸ hy))
    S k x (he S ▸ hx) hlen

end RAFCriticalWindowQuantitative
