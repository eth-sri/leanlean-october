module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialEnergy
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian
public import PDEFoundation.Calculus.RegularityOrder


/-! # Value-energy identities for classical spatial slices

The native coordinate derivatives in local integration by parts agree with the stored
scalar gradient and Hessian of the anisotropic classical carrier.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set

variable {d : ℕ}

/-- The scalar Hessian agrees with the ordered spatial derivatives of a C2 slice. -/
theorem scalarSpatialHessian_eq_spatialPartial_partial
    (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d)
    (hu : ContDiffAt ℝ 2 (fun y => u (z.1, y)) z.2) (i j : Fin d) :
    scalarSpatialHessian u z i j =
      spatialPartial i (spatialPartial j (fun y => u (z.1, y))) z.2 := by
  rw [scalarSpatialHessian_eq_secondFDeriv hu]
  unfold spatialPartial

  rw [fderiv_clm_apply ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) (differentiableAt_const (PDE.basisVec j))]
  simp

/-- Each time slice obeys the exact spatial cutoff value-energy identity. -/
theorem integral_scalar_local_spatial_value_energy_slice
    (a T : ℝ) (O : PDE.VelocityRegion d) (hO : IsOpen O)
    (u ρ : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ PDE.smoothOrder ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (t : ℝ) (ht : t ∈ Ioo a T) (i j : Fin d)
    (hA : ContDiffOn ℝ 1 (fun y => A t y i j) O) :
    (∫ y in O, A t y i j * scalarSpatialGradient u (t, y) j *
      (ρ (t, y) ^ 2 * scalarSpatialGradient u (t, y) i +
        2 * ρ (t, y) * scalarSpatialGradient ρ (t, y) i * u (t, y))) =
    -(∫ y in O, (spatialPartial i (fun x => A t x i j) y *
      scalarSpatialGradient u (t, y) j + A t y i j * scalarSpatialHessian u (t, y) i j) *
      (u (t, y) * ρ (t, y) ^ 2)) := by
  have hq : ContDiffOn ℝ 2 (fun y => u (t, y)) O :=
    fun y hy => (hu.spatialSlice_contDiffAt (show (t, y) ∈ Ioo a T ×ˢ O
      from ⟨ht, hy⟩)).contDiffWithinAt

  have hi := integral_local_spatial_value_energy_entry O hO i j
    (fun y => A t y i j) (fun y => u (t, y)) (fun y => ρ (t, y)) hA hq (hρ.comp (contDiff_const.prodMk contDiff_id))
    (hasCompactSupport_local_cutoff_time_slice ρ hc t)
    (tsupport_local_cutoff_time_slice_subset ρ hsub t)
  calc
    _ = _ := hi.trans (by
      congr 1
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      dsimp only
      rw [scalarSpatialHessian_eq_spatialPartial_partial u (t, y)
        (hu.spatialSlice_contDiffAt (show (t, y) ∈ Ioo a T ×ˢ O from ⟨ht, hy⟩)) i j]
      rfl)

end HypoellipticAleksandrov.Parabolic.LocalHolder
