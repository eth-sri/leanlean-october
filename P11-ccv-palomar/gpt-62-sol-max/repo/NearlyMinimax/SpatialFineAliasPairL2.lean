module

public import NearlyMinimax.SpatialLaplaceTail
public import NearlyMinimax.CardinalProductDesign


@[expose] public section

/-! Genuine bounded-domain pair integration of the actual fine-alias
Laplace kernel, including the real Fin2 product coordinate law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable {d : ℕ} (hd : 4 < d)
    {T0 N : ℝ} (hT0 : 0 < T0) (hN : T0 ≤ N)
include hd hT0 hN

/-- Actual Wfi² integration over the two source cube points. -/
theorem fineAlias_spatial_pair_squared_integrable_and_integral_le :
    Integrable (fun xy : CovariatePair d =>
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2))^2)
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ∧
    (∫ xy : CovariatePair d,
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance xy.1 xy.2))^2
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      6 * (2 : ℝ)^d * spatialInverseFourConstant d / T0^(d-4) := by
  have hm := ((fineAliasLaplaceKernel_measurable T0 N hN).comp
    (exactEuclideanDistance_continuous (d := d)).measurable).pow_const 2
  have h := finite_pair_kernel_integrable_and_integral_le volume (volume.restrict (spatialPatchBox d))
    Measure.restrict_le_self _ hm (fun _ => sq_nonneg _) (6*spatialInverseFourConstant d/T0^(d-4))
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hT0 hN x).1)
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hT0 hN x).2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [measureReal_def, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d) * _ = _
  rw [spatialPatchBox_real_volume]
  ring

/-- The same genuine fine-alias estimate in the paper's Fin2 tuple coordinates. -/
theorem fineAlias_fullSpatialPatchDesign_squared_integrable_and_integral_le :
    Integrable (fun U : Fin 2 → Covariate d =>
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance (U 0) (U 1)))^2)
      (fullSpatialPatchDesign d 2) ∧
    (∫ U : Fin 2 → Covariate d,
      (fineAliasLaplaceKernel T0 N (exactEuclideanDistance (U 0) (U 1)))^2
      ∂fullSpatialPatchDesign d 2) ≤
      6 * (2 : ℝ)^d * spatialInverseFourConstant d / T0^(d-4) := by
  have h := fineAlias_spatial_pair_squared_integrable_and_integral_le hd hT0 hN
  exact fullSpatialPatchDesign_pair_moments h.1 h.2

end

end NearlyMinimax
