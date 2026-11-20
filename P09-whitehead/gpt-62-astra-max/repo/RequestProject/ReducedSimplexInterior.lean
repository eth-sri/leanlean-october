module

public import RequestProject.ReducedSimplex
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

namespace FiniteChains

variable (n : ℕ)

/-- The strict-coordinate description is exactly the reduced simplex interior. -/
theorem reducedSimplex_interior_eq :
    interior (reducedSimplex n) = reducedSimplexPositive n := by
  apply Set.Subset.antisymm
  · intro x hx
    constructor
    · intro i
      have hi := interior_mono (show reducedSimplex n ⊆
          (Function.eval i) ⁻¹' Set.Ici 0 from fun _ h => h.1 i) hx
      have ht := (isOpenMap_eval i).interior_preimage_subset_preimage_interior hi
      simp_all
    · cases n with
      | zero => simp
      | succ n =>
        let L : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
          { toFun := fun y => ∑ i, y i
            map_add' := by simp [Finset.sum_add_distrib]
            map_smul' := by simp [Finset.mul_sum]
            cont := continuous_finset_sum _ (fun i _ => continuous_apply i) }
        have hs : Function.Surjective L := by
          intro r
          refine ⟨Pi.single 0 r, ?_⟩ <;> aesop
        have hi := interior_mono (show reducedSimplex (n + 1) ⊆
            L ⁻¹' Set.Iic 1 from fun _ h => h.2) hx
        have ht := (L.isOpenMap hs).interior_preimage_subset_preimage_interior hi
        aesop
  · exact interior_maximal (reducedSimplexPositive_subset n) (reducedSimplexPositive_isOpen n)

/-- Reinserted barycentric coordinates are all positive exactly on the reduced simplex interior. -/
theorem reducedSimplexToStandard_positive_iff (x : reducedSimplex n) :
    (∀ i, 0 < (reducedSimplexToStandard n x).val i) ↔ x.val ∈ interior (reducedSimplex n) := by
  rw [reducedSimplex_interior_eq]
  change (∀ i : Fin _, 0 < (Fin.cons _ x.val : Fin _ → ℝ) i) ↔
    (∀ j, 0 < x.val j) ∧ ∑ j, x.val j < 1
  constructor
  · intro h
    constructor
    · intro j
      simpa using h j.succ
    · have h0 := h 0
      simp_all
  · rintro ⟨hp, hs⟩ i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp_all

end FiniteChains
