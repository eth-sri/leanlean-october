import RequestProject.TopologicalSingular.SimplexCoordinates
import RequestProject.ReducedSimplexBall
import RequestProject.OrderNerveRealizationWeakTopology
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.Comb
open CategoryTheory Simplicial

def orderNerveSimplexClosedBallHomeomorph n :=
  (TopologicalSingular.simplexCoordinates n).trans (standardSimplexClosedBallHomeomorph n)

theorem orderNerveSimplexClosedBallHomeomorph_positive_iff n
    z :
    (∀ i, 0 < z.weights i) ↔ (orderNerveSimplexClosedBallHomeomorph n z).val ∈ Metric.ball 0 1 := standardSimplexClosedBallHomeomorph_positive_iff n
    (TopologicalSingular.simplexCoordinates n z)

/-- A genuine continuous closed-ball characteristic chart in the actual realization. -/
def orderNerveClosedBallChart {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    C((Metric.closedBall 0 1 : Set (Fin n → ℝ)), orderNerveRealization P) where
  toFun x := orderNerveRealizationSimplex P s.val
    (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm x))
  continuous_toFun := (orderNerveRealizationSimplex P s.val).hom.continuous.comp
    (continuous_uliftUp.comp (orderNerveSimplexClosedBallHomeomorph n).symm.continuous)

/-- Closed-ball and canonical simplex charts have exactly the same actual image. -/
theorem orderNerveClosedBallChart_range {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) :
    Set.range (orderNerveClosedBallChart s) = Set.range (orderNerveRealizationSimplex P s.val) := by
  ext x
  constructor
  · aesop
  · rintro ⟨z, rfl⟩
    refine ⟨orderNerveSimplexClosedBallHomeomorph n z.down, ?_⟩
    change orderNerveRealizationSimplex P s.val
      (ULift.up ((orderNerveSimplexClosedBallHomeomorph n).symm
        (orderNerveSimplexClosedBallHomeomorph n z.down))) = _
    aesop

/-- The closed-ball chart is injective. -/
theorem orderNerveClosedBallChart_injective {P} [PartialOrder P]
    {n} (s : (nerve P).nonDegenerate n) : Function.Injective (orderNerveClosedBallChart s) :=
  (orderNerveRealizationSimplex_injective s.val
    ((PartialOrder.mem_nerve_nonDegenerate_iff_injective s.val).mp s.property)).comp
      (ULift.up_injective.comp (orderNerveSimplexClosedBallHomeomorph n).symm.injective)
