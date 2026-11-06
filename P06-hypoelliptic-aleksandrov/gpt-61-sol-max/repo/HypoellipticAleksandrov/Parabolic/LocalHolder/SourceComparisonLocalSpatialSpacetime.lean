module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSlices
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialIntegrability
import HypoellipticAleksandrov.Measure.TimeVelocity
import Mathlib.MeasureTheory.Integral.Prod
public import PDEFoundation.Calculus.RegularityOrder


/-! # Spacetime spatial value-energy identity

Fubini integrates the exact classical slice identity. Compact support supplies all
integrability needed before exchanging the spatial and temporal integrals.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

/-- The spatial value-energy identity holds on the literal product-volume cylinder. -/
theorem integral_scalar_local_spatial_value_energy_spacetime {d : ℕ}
    (a T : ℝ) (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (u ρ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ PDE.smoothOrder ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A) (i j : Fin d) :
    (∫ z in Ioo a T ×ˢ O, A z.1 z.2 i j * scalarSpatialGradient u z j *
      (ρ z ^ 2 * scalarSpatialGradient u z i +
        2 * ρ z * scalarSpatialGradient ρ z i * u z)) =
    -(∫ z in Ioo a T ×ˢ O,
      (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
        A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)) := by
  let sharedTerm_11ec35ec4f := (((volume.restrict (Ioo a T)).prod (volume.restrict O)))
  let left  := fun z =>
    A z.1 z.2 i j * scalarSpatialGradient u z j *
      (ρ z ^ 2 * scalarSpatialGradient u z i +
        2 * ρ z * scalarSpatialGradient ρ z i * u z)
  let right  := fun z =>
    (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
      A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)
  have hint := integrable_scalar_local_spatial_value_energy_terms (isOpen_Ioo.prod hO)
    u ρ hu hρ hc hsub A hA i j
  have hprod : sharedTerm_11ec35ec4f =
      volume.restrict (Ioo a T ×ˢ O ) := by
    rw [volume_timeVelocity_eq_prod]
    exact Measure.prod_restrict (Ioo a T) O


  change (∫ z in Ioo a T ×ˢ O, left z) = -(∫ z in Ioo a T ×ˢ O, right z)
  rw [← hprod, integral_prod left (show Integrable left sharedTerm_11ec35ec4f by
      rw [hprod]
      exact hint.1.restrict), integral_prod right (show Integrable right sharedTerm_11ec35ec4f by
      rw [hprod]
      exact hint.2.restrict), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht


  exact integral_scalar_local_spatial_value_energy_slice a T O hO u ρ hu hρ hc hsub
    A t ht i j (((((contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)).comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)).contDiffOn)

end HypoellipticAleksandrov.Parabolic.LocalHolder
