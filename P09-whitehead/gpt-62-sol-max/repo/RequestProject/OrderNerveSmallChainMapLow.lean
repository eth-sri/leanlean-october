module

public import RequestProject.OrderNerveSmallChainBasis
public import RequestProject.NerveDegree

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular SingularSubdivision
open scoped Classical

noncomputable def orderSmallChosenVertex {P : Type} [PartialOrder P] {n : ℕ}
    (σ : OrderSmallSimplex P n) : P := σ.property.choose


/-- The comparison begins by choosing a vertex of a star containing each point. -/
noncomputable def orderSmallToNerve0 {P : Type} [PartialOrder P] :
    smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P :=
  (Finsupp.linearCombination ℤ (fun σ  =>
    FreeAbelianGroup.of [orderSmallChosenVertex σ])).comp (orderSmallChainEquiv P 0).toLinearMap

theorem orderSmallToNerve0_single {P : Type} [PartialOrder P]
    (σ : OrderSmallSimplex P 0) (r : ℤ) :
    orderSmallToNerve0 (orderSmallSingle σ r) = r • FreeAbelianGroup.of [orderSmallChosenVertex σ] := by
  simp [← orderSmallChainEquiv_symm_single, orderSmallToNerve0, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Finsupp.linearCombination_single]

theorem orderSmallToNerve0_length {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    Nerve.lengthProjection 1 (orderSmallToNerve0 c) = orderSmallToNerve0 c := by
  have he : (Nerve.lengthProjection 1).toIntLinearMap.comp orderSmallToNerve0 =
      (orderSmallToNerve0 : smallChains (orderNerveRealizationOpenStar P) 0 →ₗ[ℤ] Nerve.Ch P) := by
    apply orderSmallSingle_spans
    intro σ
    simp [orderSmallToNerve0_single]
  exact DFunLike.congr_fun he c

theorem orderSmallToNerve0_boundary {P : Type} [PartialOrder P]
    (c : smallChains (orderNerveRealizationOpenStar P) 0) :
    Nerve.bdry (orderSmallToNerve0 c) = augmentation c.val • FreeAbelianGroup.of ([] : List P) := by
  have he : Nerve.bdry.toIntLinearMap.comp orderSmallToNerve0 =
      (augmentation.comp (smallChains (orderNerveRealizationOpenStar P) 0).subtype).smulRight
        (FreeAbelianGroup.of ([])) := by
    apply orderSmallSingle_spans
    intro σ
    change Nerve.bdry (orderSmallToNerve0 (orderSmallSingle σ 1)) =
      augmentation (Finsupp.single σ.val 1) • FreeAbelianGroup.of ([])
    rw [orderSmallToNerve0_single, one_smul, augmentation_single, one_smul, Nerve.bdry_of]
    simp [Nerve.bdryOn]
  exact DFunLike.congr_fun he c

end FiniteChains.Comb
