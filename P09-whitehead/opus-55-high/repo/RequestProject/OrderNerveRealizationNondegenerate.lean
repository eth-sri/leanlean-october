import RequestProject.OrderNerveRealizationSimplices
import RequestProject.OrderNerveDimension


namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Nondegenerate simplices alone cover the actual geometric realization. -/
theorem orderNerveRealization_nonDegenerate_jointly_surjective P [PartialOrder P]
    x :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌), orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
    refine ⟨m, t, SimplexCategory.toTop.map a z, ?_⟩
    have h := congrArg (· z) (orderNerveRealizationSimplex_operator P a t.val)
    aesop
