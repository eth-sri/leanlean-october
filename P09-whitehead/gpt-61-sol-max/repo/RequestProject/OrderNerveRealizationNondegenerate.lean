import Mathlib.Tactic

import RequestProject.OrderNerveRealizationSimplices
import RequestProject.OrderNerveDimension

namespace FiniteChains.Comb
open CategoryTheory Simplicial

/-- Nondegenerate simplices alone cover the actual geometric realization. -/
theorem orderNerveRealization_nonDegenerate_jointly_surjective (P : Type) [PartialOrder P]
    (x : orderNerveRealization P) :
    ∃ (n : ℕ) (s : (nerve P).nonDegenerate n)
      (z : SimplexCategory.toTop.obj ⦋n⦌), orderNerveRealizationSimplex P s.val z = x := by
  obtain ⟨n, s, z, hz⟩ := orderNerveRealizationSimplex_jointly_surjective P x
  induction n using SimplexCategory.rec with | _ n =>
    obtain ⟨m, a, _, t, ht⟩ := (nerve P).exists_nonDegenerate s
    refine ⟨m, t, SimplexCategory.toTop.map a z, ?_⟩
    have h := congrArg (fun k => k z) (orderNerveRealizationSimplex_operator P a t.val)
    
    rw [← ht] at h
    exact h.trans hz

end FiniteChains.Comb
