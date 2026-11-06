import RequestProject.OrderNerveRealizationHausdorff


namespace FiniteChains.Comb
open CategoryTheory

/-- Closedness is detected by nondegenerate simplex preimages alone. -/
theorem orderNerveRealization_nonDegenerate_isClosed_iff P [PartialOrder P]
    A :
    IsClosed A ↔ ∀ n (s : (nerve P).nonDegenerate n),
      IsClosed (orderNerveRealizationSimplex P s.val ⁻¹' A) := by
  constructor
  · intro h n s
    exact h.preimage (orderNerveRealizationSimplex P s.val).hom.continuous
  · intro h
    apply (orderNerveRealization_isClosed_iff P A).mpr
    intro n s
    induction n using SimplexCategory.rec with | _ n =>
      obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
      have hc := (h m t).preimage (SimplexCategory.toTop.map a).hom.continuous
      convert hc using 1
      ext z
      have ha := congrArg (· z) (orderNerveRealizationSimplex_operator P a t.val)
      change orderNerveRealizationSimplex P t.val (SimplexCategory.toTop.map a z) =
        orderNerveRealizationSimplex P ((nerve P).map a.op t.val) z at ha
      simp_all

/-- The actual realization has weak topology with respect to its nondegenerate
closed simplex images, in the form required by the CW constructor. -/
theorem orderNerveRealization_isClosed_iff_inter_simplex_range P [PartialOrder P]
    A :
    IsClosed A ↔ ∀ n (s : (nerve P).nonDegenerate n),
      IsClosed (A ∩ Set.range (orderNerveRealizationSimplex P s.val)) := by
  constructor
  · intro h n s
    exact h.inter (orderNerveRealization_nonDegenerate_isClosedEmbedding s).isClosed_range
  · intro h
    apply (orderNerveRealization_nonDegenerate_isClosed_iff P A).mpr
    intro n s
    have hc := (h n s).preimage (orderNerveRealizationSimplex P s.val).hom.continuous
    simp_all
