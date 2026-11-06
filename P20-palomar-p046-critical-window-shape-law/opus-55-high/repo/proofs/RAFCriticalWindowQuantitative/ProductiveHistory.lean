module

public import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source

def fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M := revClosureAt Q S $ Fintype.card M

inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

variable {M R : Type*} [Fintype M] [DecidableEq M]

    [DecidableEq R] (Q : ReversibleCRS M R)

theorem productive_extension   (S T : Finset R) (x : M)
    (hx : x ∈ fullClosure Q S) (hnot : x ∉ fullClosure Q T) :
    ∃ r ∈ S, r ∉ T ∧ revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T := by
  have hfixed :=
    (card_closure_sub Q T $ _+1).antisymm Finset.subset_union_left
  by_contra! h
  have H k : revClosureAt Q S k ⊆ fullClosure Q T := by
    induction k with
    | zero => exact revClosureAt_mono_stage Q T $ Nat.zero_le _
    | succ k ih =>
      refine (revClosureStep_mono Q subset_rfl ih).trans $ Finset.union_subset subset_rfl
        (Finset.biUnion_subset.2 fun r hr y hy => ?_)
      have h1 : revClosureStep Q {r} (fullClosure Q T) ⊆ fullClosure Q T := by
        by_cases hrT : r ∈ T
        · exact (revClosureStep_mono Q (Finset.singleton_subset_iff.2 hrT) subset_rfl).trans
            hfixed.subset
        simp_all
      exact h1 $ Finset.mem_union_right _ $ Finset.mem_biUnion.2 ⟨r, Finset.mem_singleton_self r, hy⟩
  tauto

theorem long_target_productive_history   (length : M → ℕ)
    (hbound : ∀ T x, x ∈ fullClosure Q T → length x ≤ 2^(T.card+1))
    (S : Finset R) (k : ℕ) (x : M) (hx : x ∈ fullClosure Q S)
    (hlen : 2^(k+1) < length x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S := by
  induction k with
  | zero => exact ⟨∅, .nil, rfl, Finset.empty_subset _⟩
  | succ k ih =>
    obtain ⟨T,hT,hcard,hTS⟩ := ih $ by omega
    have := hbound T x
    obtain ⟨r,hr,hrT,hgrow⟩ := productive_extension Q S T x hx fun hh => by grind
    exact ⟨insert r T, hT.step hr hrT hgrow, by simp_all,
      Finset.insert_subset hr hTS⟩

end RAFCriticalWindowQuantitative
