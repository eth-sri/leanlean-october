module

public import RequestProject.OrderNerveSmallChainBasis


@[expose] public section

noncomputable section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

variable {P : Type} [PartialOrder P]

section

variable {n : ℕ} (σ : OrderSmallSimplex P n)
include n

def orderSmallChosenVertex := σ.property.choose

theorem orderSmallChosenVertex_mem :
    orderSmallChosenVertex σ ∈ orderNerveSingularCarrier σ.val :=
  orderNerveSingularStarIndices_subset_carrier σ.val σ.property.choose_spec

end

/-- The comparison begins by choosing a vertex of a star containing each point. -/
def orderSmallToNerve0 :=
  (Finsupp.linearCombination ℤ (fun σ : OrderSmallSimplex P 0 =>
    FreeAbelianGroup.of [orderSmallChosenVertex σ])).comp (orderSmallChainEquiv P 0).toLinearMap

variable (σ : OrderSmallSimplex P 0)

theorem orderSmallToNerve0_single (r : ℤ) :
    orderSmallToNerve0 (orderSmallSingle σ r) = r • FreeAbelianGroup.of [orderSmallChosenVertex σ] := by
  rw [← orderSmallChainEquiv_symm_single]
  simp [orderSmallToNerve0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

variable (c : smallChains (orderNerveRealizationOpenStar P) 0)

theorem orderSmallToNerve0_length :
    Nerve.lengthProjection 1 (orderSmallToNerve0 c) = orderSmallToNerve0 c := by
  have he : (Nerve.lengthProjection 1).toIntLinearMap.comp orderSmallToNerve0 =
      (orderSmallToNerve0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    simp [orderSmallToNerve0_single]
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve0_boundary :
    Nerve.bdry (orderSmallToNerve0 c) = augmentation c.val • FreeAbelianGroup.of ([]) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve0 =
      (augmentation.comp (smallChains (orderNerveRealizationOpenStar P) 0).subtype).smulRight
        (FreeAbelianGroup.of ([])) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallToNerve0 (orderSmallSingle σ 1)) =
      augmentation (Finsupp.single σ.val 1) • FreeAbelianGroup.of _
    simp [orderSmallToNerve0_single, one_smul, augmentation_single, Nerve.bdry_of, Nerve.bdryOn]
  exact DFunLike.congr_fun he c

variable (σ : OrderSmallSimplex P 1)

end FiniteChains.Comb
