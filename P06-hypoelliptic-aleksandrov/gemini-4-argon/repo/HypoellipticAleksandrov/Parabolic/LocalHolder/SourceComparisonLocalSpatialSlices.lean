module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialEnergy
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian
import HypoellipticAleksandrov.Parabolic.ScalarClassical
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support

/-! # Value-energy identities for classical spatial slices

The native coordinate derivatives in local integration by parts agree with the stored
scalar gradient and Hessian of the anisotropic classical carrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set
open Filter
open scoped Topology

/- The scalar Hessian agrees with the ordered spatial derivatives of a C2 slice. -/
theorem integral_scalar_local_spatial_value_energy_slice {d }
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (u ρ : TimeVelocity d → ℝ)
    (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
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
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun y => ρ (t, y)) :=
    hρ.comp (contDiff_const.prodMk contDiff_id)
  have _h_xinl_0 : HasCompactSupport (fun y => ρ (t, y)) := by
    apply hc.comp_isClosedEmbedding
    refine ⟨isEmbedding_prodMkRight t, ?_⟩
    have hrange : Set.range (fun y : PDE.Vec d => (t, y)) = {t} ×ˢ univ := by
      simp only [singleton_prod, image_univ]
    rw [hrange]
    exact isClosed_singleton.prod isClosed_univ
  have hi := integral_local_spatial_value_energy_entry O hO i j
    (fun y => A t y i j) (fun y => u (t, y)) (fun y => ρ (t, y)) hA hq hη
    _h_xinl_0
    (tsupport_local_cutoff_time_slice_subset ρ hsub t)
  calc
    _ = _ := hi.trans (by
      congr 1
      apply setIntegral_congr_fun hO.measurableSet
      intro y hy
      dsimp only
      have _h_inl_8 : scalarSpatialHessian u (t, y) i j =
      spatialPartial i (spatialPartial j (fun y => u ((t, y).1, y))) (t, y).2 := by
        let z := (t, y)
        have hu := (hu.spatialSlice_contDiffAt (show (t, y) ∈ Ioo a T ×ˢ O from ⟨ht, hy⟩))
        rw [scalarSpatialHessian_eq_secondFDeriv hu]
        unfold spatialPartial
        have hd :=
          (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
        rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec j))]
        simp
      rw [_h_inl_8]
      rfl)

end HypoellipticAleksandrov.Parabolic.LocalHolder
