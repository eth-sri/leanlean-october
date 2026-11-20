module

public import RequestProject.OrderNerveGradedBoundary
public import RequestProject.OrderNerveTightChainMap
public import RequestProject.OrderNerveSingularCarrierExactness

@[expose] public section


namespace FiniteChains.Comb
open CategoryTheory TopologicalSingular SingularSubdivision
variable {P : Type} [PartialOrder P]

/-- Realization of the carried small-chain approximation in every degree. -/
noncomputable def orderSmallSingularApproximation (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) n :=
  (orderNerveGradedRealize P n).comp (orderTightToNerve P n)

theorem orderSmallSingularApproximation_boundary (n : ℕ)
    (c : smallChains (orderNerveRealizationOpenStar P) (n + 1)) :
    boundary n (orderSmallSingularApproximation P (n + 1) c) =
      orderSmallSingularApproximation P n (smallBoundary (orderNerveRealizationOpenStar P) n c) := by
  change boundary n (orderNerveGradedRealize P (n + 1) (orderTightToNerve P (n + 1) c)) = _
  rw (config := { transparency := .default }) [orderNerveGradedRealize_boundary n (orderTightToNerve_mem_inc (n + 1) c),
    orderTightToNerve_boundary]
  rfl

theorem orderSmallSingularApproximation_carrier (n : ℕ) (σ : OrderSmallSimplex P n) :
    orderSmallSingularApproximation P n (orderSmallSingle σ 1) ∈
      orderSingularCarrierChains σ.val n :=
  orderNerveGradedRealize_supported n _ (Nerve.incOn_mono (fun _ hp => hp.2) (orderTightToNerve_carrier n σ))

theorem orderSmallSingularApproximation_zero (σ : OrderSmallSimplex P 0) :
    orderSmallSingularApproximation P 0 (orderSmallSingle σ 1) =
      Finsupp.single (orderNerveSingularSimplex (ComposableArrows.mk₀ (orderSmallChosenVertex σ))) 1 := by
  change orderNerveGradedRealize P 0 (orderSmallToNerve0 (orderSmallSingle σ 1)) = _
  rw (config := { transparency := .default }) [orderSmallToNerve0_single, one_smul]
  have hl : orderNerveVertexList (ComposableArrows.mk₀ (orderSmallChosenVertex σ)) =
      [orderSmallChosenVertex σ] := by simp [orderNerveVertexList, List.ofFn_succ]
  change (orderNerveExplicitSingularMap P).f 0
    (orderNerveGradedDecode 0 (FreeAbelianGroup.of [orderSmallChosenVertex σ])) = _
  rw (config := { transparency := .default }) [← hl,
    orderNerveGradedDecode_of_vertexList, orderNerveExplicitSingularMap_single]

/-- A carried linear map sends every simplex boundary into the parent carrier. -/
theorem orderSmallBoundary_map_carrier {P : Type} [PartialOrder P] {n k : ℕ}
    (H : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) k)
    (hH : ∀ τ : OrderSmallSimplex P n,
      H (orderSmallSingle τ 1) ∈ orderSingularCarrierChains τ.val k)
    (σ : OrderSmallSimplex P (n + 1)) :
    H (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      orderSingularCarrierChains σ.val k := by
  rw [orderSmallSingle_boundary, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact orderSingularCarrierChains_face σ.val i k (hH (orderSmallSimplexFace i σ))

end FiniteChains.Comb

