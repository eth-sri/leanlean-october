module

public import RequestProject.OrderNerveGradedBoundary
public import RequestProject.OrderNerveTightChainMap
public import RequestProject.OrderNerveSmallSingularApproximation

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Realization of the carried small-chain approximation in every degree. -/
noncomputable def orderSmallSingularApproximation (P : Type) [PartialOrder P] (n : ℕ) :=
  (orderNerveGradedRealize P n).comp (orderTightToNerve P n)

variable (n : ℕ)

theorem orderSmallSingularApproximation_boundary
    (c : smallChains (orderNerveRealizationOpenStar P) _) :
    boundary n (orderSmallSingularApproximation P _ c) =
      orderSmallSingularApproximation P n (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  erw [orderNerveGradedRealize_boundary n (orderTightToNerve_mem_inc _ c),
    orderTightToNerve_boundary]; rfl

theorem orderSmallSingularApproximation_carrier (σ : OrderSmallSimplex P n) :
    orderSmallSingularApproximation P n (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val n :=
  orderNerveGradedRealize_supported n _ (Nerve.incOn_mono (fun _ hp => hp.2) (orderTightToNerve_carrier n σ))

theorem orderSmallSingularApproximation_zero :
    orderSmallSingularApproximation P 0 = orderSmallSingularApproximation0 := by
  apply orderSmallSingle_spans
  intro σ
  change orderNerveGradedRealize P 0 _ = _
  erw [orderSmallToNerve0_single, one_smul, orderSmallSingularApproximation0_single]
  have hl : orderNerveVertexList (ComposableArrows.mk₀ (orderSmallChosenVertex σ)) =
      [orderSmallChosenVertex σ] := by simp [orderNerveVertexList, List.ofFn_succ]
  change (orderNerveExplicitSingularMap P).f 0
    _ = _
  erw [orderNerveGradedDecode_of, ← hl, orderNerveGradedDecodeList_vertexList,
    orderNerveExplicitSingularMap_single]
  rfl

end FiniteChains.Comb
