module




public import RequestProject.OrderNerveSmallHomotopyZero
public import RequestProject.OrderNerveOneDecoding

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision

variable {P : Type} [PartialOrder P]

/-- A carried linear map sends every simplex boundary into the parent carrier. -/
theorem orderSmallBoundary_map_carrier {n k : ℕ}
    (H : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] Chain (orderNerveRealization P) k)
    (hH : ∀ τ : OrderSmallSimplex P n,
      H (orderSmallSingle τ 1) ∈ orderSingularCarrierChains τ.val k)
    (σ : OrderSmallSimplex P _) :
    H (smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ 1)) ∈
      orderSingularCarrierChains σ.val k := by
  rw [orderSmallSingle_boundary, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact orderSingularCarrierChains_face σ.val i k (hH (orderSmallSimplexFace i σ))

end FiniteChains.Comb
