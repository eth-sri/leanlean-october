module

public import RequestProject.OrderNerveRealizationHausdorff

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial

variable (P : Type) [PartialOrder P] (A : Set (orderNerveRealization P))

/-- Closedness is detected by nondegenerate simplex preimages alone. -/
theorem orderNerveRealization_nonDegenerate_isClosed_iff :
    IsClosed A ↔ ∀ (n : ℕ) (s : (nerve P).nonDegenerate n),
      IsClosed (orderNerveRealizationSimplex P s.val ⁻¹' A) := by
  constructor
  · intro h n s
    exact h.preimage (orderNerveRealizationSimplex P s.val).hom.continuous
  · intro h
    apply (orderNerveRealization_isClosed_iff P A).mpr
    intro n s
    induction n using SimplexCategory.rec with | _ n =>
      obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
      convert ((h m t).preimage (SimplexCategory.toTop.map a).hom.continuous) using 1
      ext z
      have ha := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a t.val)
      rw [← ht] at ha; exact iff_of_eq (congrArg (fun x => x ∈ A) ha.symm)

/-- The actual realization has weak topology with respect to its nondegenerate
closed simplex images, in the form required by the CW constructor. -/
theorem orderNerveRealization_isClosed_iff_inter_simplex_range :
    IsClosed A ↔ ∀ (n : ℕ) (s : (nerve P).nonDegenerate n),
      IsClosed (A ∩ Set.range (orderNerveRealizationSimplex P s.val)) := by
  constructor
  · intro h n s
    exact h.inter (orderNerveRealization_nonDegenerate_isClosedEmbedding s).isClosed_range
  · intro h
    apply (orderNerveRealization_nonDegenerate_isClosed_iff P A).mpr
    intro n s
    convert ((h n s).preimage (orderNerveRealizationSimplex P s.val).hom.continuous) using 1
    simp

end FiniteChains.Comb
