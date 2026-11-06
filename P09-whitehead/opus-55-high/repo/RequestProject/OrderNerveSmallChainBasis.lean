import RequestProject.OrderNerveRealizationSmallChains
import RequestProject.OrderNerveSingularCarrierFillings
noncomputable section


namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

/-- Singular simplices whose whole image is contained in an open vertex star. -/
abbrev OrderSmallSimplex (P : Type) [PartialOrder P] (n : ℕ) :=
  {σ : TopologicalSingular.Simplex (orderNerveRealization P) n //
    (orderNerveSingularStarIndices σ).Nonempty}

/-- The small-chain submodule is genuinely free on the small singular simplices. -/
def orderSmallChainEquiv P [PartialOrder P] n :
    smallChains (orderNerveRealizationOpenStar P) n ≃ₗ[ℤ] (OrderSmallSimplex P n →₀ ℤ) :=
  Finsupp.supportedEquivFinsupp _

def orderSmallSimplexFace {P} [PartialOrder P] {n}
    (i : Fin (n + 2)) (σ : OrderSmallSimplex P (n + 1)) : OrderSmallSimplex P n :=
  ⟨TopologicalSingular.face i σ.val, by
    cases' σ.property with v hv
    tauto⟩

def orderSmallSingle {P} [PartialOrder P] {n}
    (σ : OrderSmallSimplex P n) (r : ℤ) : smallChains (orderNerveRealizationOpenStar P) n :=
  ⟨Finsupp.single σ.val r, Finsupp.single_mem_supported ℤ r σ.property⟩

theorem orderSmallChainEquiv_symm_single {P} [PartialOrder P] {n}
    σ r :
    (orderSmallChainEquiv P n).symm (Finsupp.single σ r) = orderSmallSingle σ r := by
  apply Subtype.ext
  exact Finsupp.supportedEquivFinsupp_symm_single _ σ r

/-- The free small-chain basis has the actual alternating singular differential. -/
theorem orderSmallSingle_boundary {P} [PartialOrder P] {n}
    σ r :
    smallBoundary (orderNerveRealizationOpenStar P) n (orderSmallSingle σ r) =
      ∑ i : Fin (n + 2), (-1) ^ i.val • orderSmallSingle (orderSmallSimplexFace i σ) r := by
  apply Subtype.ext
  change TopologicalSingular.boundary n (Finsupp.single σ.val r) = _
  simp only [TopologicalSingular.boundary_single, Submodule.coe_sum, Submodule.coe_smul]
  rfl

theorem orderSmallSingle_spans {P} [PartialOrder P] {n : ℕ}
    {M} [AddCommMonoid M] [Module ℤ M]
    (f g : smallChains (orderNerveRealizationOpenStar P) n →ₗ[ℤ] M)
    (h : ∀ σ : OrderSmallSimplex P n, f (orderSmallSingle σ 1) = g (orderSmallSingle σ 1)) :
    f = g := by
  apply LinearMap.ext
  intro c
  have he : f.comp (orderSmallChainEquiv P n).symm.toLinearMap =
      g.comp (orderSmallChainEquiv P n).symm.toLinearMap := by
    apply Finsupp.lhom_ext
    intro σ r
    have hs : Finsupp.single σ r = r • Finsupp.single σ 1 := by simp
    rw [hs, map_smul, map_smul]
    simp_all [LinearMap.comp_apply, LinearEquiv.coe_coe, orderSmallChainEquiv_symm_single]
  simp_all

/-- The basis carriers decrease along every face. -/
theorem orderSmallSimplexFace_carrier {P} [PartialOrder P] {n}
    i (σ : OrderSmallSimplex P (n + 1)) :
    orderNerveSingularCarrier (orderSmallSimplexFace i σ).val ⊆ orderNerveSingularCarrier σ.val :=
  orderNerveSingularCarrier_face σ.val i
