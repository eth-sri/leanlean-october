module

public import proofs.RAFCriticalWindowQuantitative.FiniteClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer

def settledChannels {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)
    (S : Finset R) (C : Finset M) : Finset R :=
  S.filter (fun r => Q.lhs r ⊆ C ∧ Q.rhs r ⊆ C)

theorem growing_closure_grows_settled {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (C : Finset M)
    (hg : revClosureStep Q S C ≠ C) :
    (settledChannels Q S C).card < (settledChannels Q S (revClosureStep Q S C)).card := by
  have hold : C ⊆ revClosureStep Q S C := Finset.subset_union_left
  obtain ⟨x, hx, hnot⟩ := Finset.not_subset.mp fun hh => hg (Finset.Subset.antisymm hh hold)
  obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp hx).resolve_left hnot)
  have ⟨hns, hs⟩ : r ∉ settledChannels Q S C ∧ r ∈ settledChannels Q S (revClosureStep Q S C) := by
    rcases Finset.mem_union.mp hxr with hxL | hxR
    · by_cases hL : RevEnabledLhs Q C r <;> simp only [hL, ↓reduceIte, Finset.notMem_empty] at hxL
      exact ⟨fun hs => hnot ((Finset.mem_filter.mp hs).2.2 hxL), Finset.mem_filter.mpr ⟨hr, hL.trans hold,
        fun _ hy => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_union_left _ (ite_eq_left hL ▸ hy)⟩)⟩⟩
    · by_cases hR : RevEnabledRhs Q C r <;> simp only [hR, ↓reduceIte, Finset.notMem_empty] at hxR
      exact ⟨fun hs => hnot ((Finset.mem_filter.mp hs).2.1 hxR), Finset.mem_filter.mpr ⟨hr,
        fun _ hy => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_union_right _ (ite_eq_left hR ▸ hy)⟩), hR.trans hold⟩⟩
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨fun _ h => let ⟨h1, h2, h3⟩ := Finset.mem_filter.mp h; Finset.mem_filter.mpr ⟨h1, h2.trans hold, h3.trans hold⟩,
     fun he => hns (he.symm ▸ hs)⟩)

theorem crs_iteration_length {N : ℕ} {R : Type*} [DecidableEq R] (Q : ReversibleCRS (Molecule N) R)
    (hfood : Q.food = binaryFood N 2)
    (hchan : ∀ r : R, ∃ l ri p : Molecule N,
      Q.lhs r = {l, ri} ∧ Q.rhs r = {p} ∧ molLength l + molLength ri = molLength p)
    (S : Finset R) (x : Molecule N) (hx : x ∈ Finset.univ.filter fun x => ∃ k, x ∈ revClosureAt Q S k) :
    molLength x ≤ 2^(S.card+1) := by
  have hgs (k : ℕ) : k ≤ (settledChannels Q S (revClosureAt Q S k)).card ∨
      revClosureAt Q S (k+1) = revClosureAt Q S k := by
    induction k with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ k ih =>
      by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
      · exact Or.inr (by change revClosureStep Q S (revClosureAt Q S (k+1)) = _; rw [he]; exact he)
      · exact Or.inl ((ih.resolve_right he).trans_lt (growing_closure_grows_settled Q S _ he))
  have hstab : revClosureAt Q S (S.card+1) = revClosureAt Q S S.card := by
    by_contra hn
    have hg := (hgs S.card).resolve_right hn
    have hh := growing_closure_grows_settled Q S (revClosureAt Q S S.card) hn
    have hbound : (settledChannels Q S (revClosureStep Q S (revClosureAt Q S S.card))).card ≤ S.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  rw [filter_revClosureAt_eq_of_stable _ S hstab] at hx
  have hiter (k : ℕ) : ∀ y ∈ revClosureAt Q S k, molLength y ≤ 2^(k+1) := by
    induction k with
    | zero => intro y hy; dsimp [revClosureAt] at hy; rw [hfood] at hy; exact (Finset.mem_filter.mp hy).2
    | succ k ih =>
      intro y hy
      have hinc : 2^(k+1) ≤ 2^(k+1+1) := by rw [pow_succ]; omega
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (ih y hy).trans hinc
      · obtain ⟨r, _, hy⟩ := Finset.mem_biUnion.mp hy
        obtain ⟨l, ri, p, hlhs, hrhs, hlen⟩ := hchan r
        rcases Finset.mem_union.mp hy with hy | hy
        · by_cases hen : RevEnabledLhs Q (revClosureAt Q S k) r <;> simp only [hen, ↓reduceIte, hrhs, Finset.mem_singleton, Finset.notMem_empty] at hy
          subst hy
          have hl := ih l (hen (hlhs ▸ Finset.mem_insert_self _ _))
          have hr := ih ri (hen (hlhs ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          rw [pow_succ]; omega
        · by_cases hen : RevEnabledRhs Q (revClosureAt Q S k) r <;> simp only [hen, ↓reduceIte, hlhs, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at hy
          have hp := ih p (hen (hrhs ▸ Finset.mem_singleton_self _))
          rcases hy with rfl | rfl <;> omega
  exact hiter S.card x hx

theorem sparse_closure_length (N : ℕ) (S : Finset (Reaction N))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure 2 S) :
    molLength x ≤ 2^(S.card+1) :=
  crs_iteration_length (binaryPolymerCRS N 2) rfl
    (fun r => ⟨reactionLeft r, reactionRight r, reactionProduct r, rfl, rfl, by
      simp [molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct, reaction_length_add]⟩)
    S x hx

end RAFCriticalWindowQuantitative
