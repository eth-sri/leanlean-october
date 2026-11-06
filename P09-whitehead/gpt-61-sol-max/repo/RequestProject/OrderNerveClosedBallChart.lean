import Mathlib.Tactic

import RequestProject.TopologicalSingular.SimplexCoordinates
import RequestProject.ReducedSimplexBall
import RequestProject.OrderNerveRealizationWeakTopology

namespace FiniteChains.Comb
open CategoryTheory Simplicial

noncomputable def orderNerveSimplexClosedBallHomeomorph (n : ℕ)  :=
  (TopologicalSingular.simplexCoordinates n).trans (standardSimplexClosedBallHomeomorph n)

theorem orderNerveSimplexClosedBallHomeomorph_positive_iff (n : ℕ)
    (z : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (∀ i, 0 < z.weights i) ↔ (orderNerveSimplexClosedBallHomeomorph n z).val ∈ Metric.ball 0 1 := standardSimplexClosedBallHomeomorph_positive_iff n
    (TopologicalSingular.simplexCoordinates n z)

variable {P : Type}
/-- A genuine continuous closed-ball characteristic chart in the actual realization. -/
noncomputable def orderNerveClosedBallChart  [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    C((Metric.closedBall 0 1 : Set (Fin n → ℝ)), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P s.val
    (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm x))
  continuous_toFun := (orderNerveRealizationSimplex P s.val).hom.continuous.comp
    (continuous_uliftUp.comp (orderNerveSimplexClosedBallHomeomorph n).symm.continuous)

/-- Closed-ball and canonical simplex charts have exactly the same actual image. -/
theorem orderNerveClosedBallChart_range  [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n) :
    Set.range (orderNerveClosedBallChart s) = Set.range (orderNerveRealizationSimplex P s.val) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨orderNerveSimplexClosedBallHomeomorph n z.down, ?_⟩
    change orderNerveRealizationSimplex P s.val
      (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm
        (orderNerveSimplexClosedBallHomeomorph n z.down))) = _
    rw [Homeomorph.symm_apply_apply]
    rfl

/-- The closed-ball chart is injective. -/
abbrev orderNerveClosedBallChart_injective  [PartialOrder P]
    {n : ℕ} (s : (nerve P).nonDegenerate n)  :=
  (orderNerveRealizationSimplex_injective s.val
    ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property)).comp
      (ULift.up_injective.comp (orderNerveSimplexClosedBallHomeomorph n).symm.injective)

end FiniteChains.Comb
