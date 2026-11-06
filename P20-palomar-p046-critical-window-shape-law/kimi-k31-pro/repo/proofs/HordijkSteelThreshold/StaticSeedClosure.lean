module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- Induction over actual reversible generation, including both reaction directions. -/
theorem temporaryReactionClosure_induction {N L : ℕ} (S : Finset (Reaction N))
    (P : Molecule N → Prop)
    (hfood : ∀ x, molLength x ≤ L → P x)
    (hlig : ∀ r ∈ S, P (reactionLeft r) → P (reactionRight r) → P (reactionProduct r))
    (hcleave : ∀ r ∈ S, P (reactionProduct r) → P (reactionLeft r) ∧ P (reactionRight r))
    (x : Molecule N) (hx : x ∈ temporaryReactionClosure L S) : P x := by
  obtain ⟨k, hk⟩ := (mem_temporaryReactionClosure S x).mp hx
  have hall : ∀ k, ∀ x ∈ revClosureAt (binaryPolymerCRS N L) S k, P x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact hfood x (by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hx)
    | succ k ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ih x hx
      · obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
        rcases Finset.mem_union.mp hx with hx | hx
        · by_cases hen : RevEnabledLhs (binaryPolymerCRS N L)
              (revClosureAt (binaryPolymerCRS N L) S k) r
          · rw [ite_eq_left hen] at hx
            have he : x = reactionProduct r := Finset.mem_singleton.mp hx
            subst x
            have hh : reactionLeft r ∈ revClosureAt (binaryPolymerCRS N L) S k ∧
                reactionRight r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
              simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff,
                Finset.singleton_subset_iff] using hen
            exact hlig r hr (ih _ hh.1) (ih _ hh.2)
          · simp [hen] at hx
        · by_cases hen : RevEnabledRhs (binaryPolymerCRS N L)
              (revClosureAt (binaryPolymerCRS N L) S k) r
          · rw [ite_eq_left hen] at hx
            have hp : reactionProduct r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
              simpa [RevEnabledRhs, binaryPolymerCRS] using hen
            have hh := hcleave r hr (ih _ hp)
            have he : x = reactionLeft r ∨ x = reactionRight r := by
              simpa [binaryPolymerCRS] using hx
            rcases he with rfl | rfl
            · exact hh.1
            · exact hh.2
          · simp [hen] at hx
  exact hall k x hk

/-- Once a smaller-food closure generates the supplied seed, it contains every
generation using that seed and any subset of its reactions. -/
theorem temporaryReactionClosure_seed_transfer {N L K : ℕ}
    {S T : Finset (Reaction N)} (hST : S ⊆ T)
    (hseed : ∀ x, molLength x ≤ L → x ∈ temporaryReactionClosure K T) :
    temporaryReactionClosure L S ⊆ temporaryReactionClosure K T := by
  intro x hx
  exact temporaryReactionClosure_induction S (fun y => y ∈ temporaryReactionClosure K T)
    hseed (fun r hr => temporaryReactionClosure_ligation T r (hST hr))
    (fun r hr => temporaryReactionClosure_cleavage T r (hST hr)) x hx

end HordijkSteelThreshold
