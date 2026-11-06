import Mathlib.Tactic

import RequestProject.OrderNerveRealizationSmallChains
import RequestProject.OrderNerveSingularCarrierFillings

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision


/-- Singular simplices whose whole image is contained in an open vertex star. -/
abbrev OrderSmallSimplex (P : Type) [PartialOrder P] (n : ℕ) :=
  {σ : TopologicalSingular.Simplex (orderNerveRealization P) n //
    (orderNerveSingularStarIndices σ).Nonempty}

/-- The small-chain submodule is genuinely free on the small singular simplices. -/
noncomputable def orderSmallChainEquiv (P : Type) [PartialOrder P] (n : ℕ) :
    smallChains (orderNerveRealizationOpenStar P) n ≃ₗ[ℤ] (OrderSmallSimplex P n →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp _

variable {P : Type}
noncomputable def orderSmallSimplexFace  [PartialOrder P] {n : ℕ}
    (i : Fin (n + 2)) (σ : OrderSmallSimplex P (n + 1)) : OrderSmallSimplex P n :=
  ⟨TopologicalSingular.face i σ.val, by
    obtain ⟨v, hv⟩ := σ.property
    exact ⟨v, orderNerveSingularStarIndices_face σ.val i hv⟩⟩

noncomputable def orderSmallSingle  [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) (r : ℤ) : smallChains (orderNerveRealizationOpenStar P) n :=
  ⟨Finsupp.single σ.val r, Finsupp.single_mem_supported ℤ r σ.property⟩

theorem orderSmallChainEquiv_symm_single  [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) (r : ℤ) :
    (orderSmallChainEquiv P n).symm (Finsupp.single σ r) = orderSmallSingle σ r := by
  apply Subtype.ext
  exact Finsupp.supportedEquivFinsupp_symm_single _ σ r

/-- The free small-chain basis has the actual alternating singular differential. -/
theorem orderSmallSingle_boundary  [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P (n + 1)) (r : ℤ) :
    smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ r) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • orderSmallSingle (orderSmallSimplexFace i σ) r := by
  apply Subtype.ext
  change TopologicalSingular.boundary n (Finsupp.single σ.val r) = _
  simp only [TopologicalSingular.boundary_single, Submodule.coe_sum]
  rfl

theorem orderSmallSingle_spans  [PartialOrder P] {n : ℕ}
    {M : Type*} [AddCommMonoid M] [Module ℤ M]
    (f g : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] M)
    (h : ∀ σ : OrderSmallSimplex P n, f (orderSmallSingle σ 1) = g (orderSmallSingle σ 1)) :
    f = g := by
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ := (orderSmallChainEquiv P n).symm.surjective c
  have he : f.comp (orderSmallChainEquiv P n).symm.toLinearMap =
      g.comp (orderSmallChainEquiv P n).symm.toLinearMap := by
    ext <;> simp_all [orderSmallChainEquiv_symm_single]
  exact DFunLike.congr_fun he d

/-- The basis carriers decrease along every face. -/
abbrev orderSmallSimplexFace_carrier  [PartialOrder P] {n : ℕ}
    (i : Fin (n + 2)) (σ : OrderSmallSimplex P (n + 1))  :=
  orderNerveSingularCarrier_face σ.val i

end FiniteChains.Comb
