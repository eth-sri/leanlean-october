module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- Induction over actual reversible generation, including both reaction directions. -/
theorem temporaryReactionClosure_induction {N L : ℕ} (S : Finset $ Reaction N)
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
      exact hfood x $ by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hx
    | succ k ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · simp_all
      · obtain ⟨r, hr, hx⟩ := Finset.mem_biUnion.mp hx
        rcases Finset.mem_union.mp hx with hx | hx
        · by_cases hen : RevEnabledLhs (binaryPolymerCRS N L)
              (revClosureAt (binaryPolymerCRS N L) S k) r
          · rw [ite_eq_left hen] at hx
            have he := Finset.mem_singleton.mp hx
            have hh : reactionLeft r ∈ revClosureAt (binaryPolymerCRS N L) S k ∧
                reactionRight r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
              simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff] using hen
            grind
          grind
        · by_cases hen : RevEnabledRhs (binaryPolymerCRS N L)
              (revClosureAt (binaryPolymerCRS N L) S k) r
          · rw [ite_eq_left hen] at hx
            have hp : reactionProduct r ∈ revClosureAt (binaryPolymerCRS N L) S k := by
              tauto
            have he : x = reactionLeft r ∨ x = reactionRight r := by
              simpa [binaryPolymerCRS] using hx
            grind
          grind
  grind

/-- Once a smaller-food closure generates the supplied seed, it contains every
generation using that seed and any subset of its reactions. -/
theorem temporaryReactionClosure_seed_transfer {N L K : ℕ}
    {S T : Finset $ Reaction N} (hST : S ⊆ T)
    (hseed : ∀ x, molLength x ≤ L → x ∈ temporaryReactionClosure K T) :
    temporaryReactionClosure L S ⊆ temporaryReactionClosure K T := by
  intro x hx
  exact temporaryReactionClosure_induction S (· ∈ temporaryReactionClosure K T)
    hseed (fun r hr => temporaryReactionClosure_ligation T r $ hST hr)
    (fun r hr => temporaryReactionClosure_cleavage T r $ hST hr) x hx

end HordijkSteelThreshold
