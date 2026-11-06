module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

theorem temporaryReactionClosure_induction {N L : ℕ} (S : Finset (Reaction N))
    (P : Molecule N → Prop)
    (hfood : ∀ x, molLength x ≤ L → P x)
    (hlig : ∀ r ∈ S, P (reactionLeft r) → P (reactionRight r) → P (reactionProduct r))
    (hcleave : ∀ r ∈ S, P (reactionProduct r) → P (reactionLeft r) ∧ P (reactionRight r))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L S) : P x := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  clear hx
  induction k generalizing x with
  | zero => exact hfood x (by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hk)
  | succ k ih =>
    rcases Finset.mem_union.mp hk with hk | hk
    · exact ih x hk
    · obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hk
      rcases Finset.mem_union.mp hx with hx | hx <;> split_ifs at hx with hen
      · obtain rfl : x = reactionProduct r := Finset.mem_singleton.mp hx
        obtain ⟨hl, hr'⟩ : reactionLeft r ∈ _ ∧ reactionRight r ∈ _ := by
          simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff] using hen
        exact hlig r hr (ih _ hl) (ih _ hr')
      · simp at hx
      · have hh := hcleave r hr (ih _ (by simpa [RevEnabledRhs, binaryPolymerCRS] using hen))
        rcases (by simpa [binaryPolymerCRS] using hx : x = reactionLeft r ∨ x = reactionRight r) with rfl | rfl
        · exact hh.1
        · exact hh.2
      · simp at hx

theorem temporaryReactionClosure_seed_transfer {N L K : ℕ}
    {S T : Finset (Reaction N)} (hST : S ⊆ T)
    (hseed : ∀ x, molLength x ≤ L → x ∈ temporaryReactionClosure K T) :
    temporaryReactionClosure L S ⊆ temporaryReactionClosure K T :=
  fun x => temporaryReactionClosure_induction S _ hseed
    (fun r hr => temporaryReactionClosure_ligation T r (hST hr))
    (fun r hr => temporaryReactionClosure_cleavage T r (hST hr)) x

end HordijkSteelThreshold
