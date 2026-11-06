import RequestProject.OrderNerveGradedBoundary
import RequestProject.OrderNerveSmallChainMapAll
import RequestProject.OrderNerveSmallSingularApproximation
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Realization of the carried small-chain approximation in every degree. -/
noncomputable def orderSmallSingularApproximation P [PartialOrder P] n :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  (orderNerveGradedRealize P n).comp (orderSmallToNerve P n)

theorem orderSmallSingularApproximation_boundary n
    c :
    boundary n (orderSmallSingularApproximation P (n + 1) c) =
      orderSmallSingularApproximation P n (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  rwd [orderNerveGradedRealize_boundary n (orderSmallToNerve_mem_inc _ c),
    orderSmallToNerve_boundary]
  rfl

theorem orderSmallSingularApproximation_carrier n σ :
    orderSmallSingularApproximation P n (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val n :=
  orderNerveGradedRealize_supported n _ (orderSmallToNerve_carrier n σ)

theorem orderSmallSingularApproximation_zero :
    orderSmallSingularApproximation P 0 = orderSmallSingularApproximation0 := by
  apply orderSmallSingle_spans
  intro σ
  change orderNerveGradedRealize P 0 (orderSmallToNerve0 (orderSmallSingle σ 1)) = _
  rwd [orderSmallToNerve0_single, one_smul, orderSmallSingularApproximation0_single]
  have hl : orderNerveVertexList (ComposableArrows.mk₀ (orderSmallChosenVertex σ)) =
      [orderSmallChosenVertex σ] := by rfl
  change (orderNerveExplicitSingularMap P).f 0
    (orderNerveGradedDecode 0 (FreeAbelianGroup.of [orderSmallChosenVertex σ])) = _
  rwd [orderNerveGradedDecode_of, ← hl, orderNerveGradedDecodeList_vertexList,
    orderNerveExplicitSingularMap_single]
  rfl
