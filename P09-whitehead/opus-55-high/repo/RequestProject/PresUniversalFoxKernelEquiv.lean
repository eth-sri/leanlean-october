import RequestProject.PresUniversalFoxColumns
noncomputable section


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} [DecidableEq α] (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Actual relator-chain coordinates in the cell-indexed presentation group ring. -/
def presUniversalRelatorRingEquiv :=
  (presUniversalRelatorGroupChainEquiv ρ w hw hpos).trans
    (groupCellChainEquiv (I := J))

/-- Actual generator-chain coordinates in the cell-indexed presentation group ring. -/
def presUniversalGeneratorRingEquiv :=
  (presUniversalGeneratorGroupChainEquiv ρ w hw hpos).trans
    (groupCellChainEquiv (I := α))

/-- The actual geometric boundary commutes with the proved Fox coordinate equivalences. -/
theorem presUniversalFox_coordinates_commute
    c :
    presUniversalGeneratorRingEquiv ρ w hw hpos
      (presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos) c) =
      coverSecondBoundary (relSub ρ) ρ (presUniversalRelatorRingEquiv ρ w hw hpos c) := by
  have h := LinearMap.congr_fun (presUniversalGroupRingBoundary_eq_fox ρ w hw hpos)
    (presUniversalRelatorRingEquiv ρ w hw hpos c)
  simp_all [presUniversalGroupRingBoundary, presUniversalGroupBoundary, presUniversalRelatorRingEquiv, presUniversalGeneratorRingEquiv, LinearEquiv.trans_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply]

/-- The genuine universal geometric generator-boundary kernel is the actual Fox kernel. -/
def presUniversalGeneratorFoxKernelEquiv :
    LinearMap.ker (presCoverRelatorGeneratorBoundary (P := UOrder (PresPos w) (ptBase w))
      w uOrderEnd (presUniversalEnd_isPosetCover w hpos)) ≃ₗ[ℤ]
    LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ) where
  toFun c := ⟨presUniversalRelatorRingEquiv ρ w hw hpos c.val, by
    simp [← presUniversalFox_coordinates_commute]⟩
  invFun c := ⟨(presUniversalRelatorRingEquiv ρ w hw hpos).symm c.val, by
    apply (presUniversalGeneratorRingEquiv ρ w hw hpos).injective
    rw [map_zero, presUniversalFox_coordinates_commute, LinearEquiv.apply_symm_apply]
    exact c.property⟩
  left_inv c := Subtype.ext ((presUniversalRelatorRingEquiv ρ w hw hpos).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((presUniversalRelatorRingEquiv ρ w hw hpos).apply_symm_apply c.val)
  map_add' c d := Subtype.ext (map_add _ c.val d.val)
  map_smul' n c := Subtype.ext (map_smul _ n c.val)

/-- Actual strict universal presentation two-cycles have the genuine algebraic Fox kernel coordinates. -/
def presUniversalTwoCycleFoxKernelEquiv :=
  (presCoverCycleRelatorGeneratorKernelEquiv w uOrderEnd
    _ hpos).trans
      (presUniversalGeneratorFoxKernelEquiv ρ w hw hpos)
