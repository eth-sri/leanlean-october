/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InfinityChart
public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import Mathlib.Geometry.Euclidean.Inversion.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! The compactifying reference measure is invariant under planar inversion. -/

@[expose] public section

open MeasureTheory
open scoped Topology RealInnerProductSpace ENNReal
open EuclideanGeometry DOZZ DOZZ.Proofs

namespace DOZZ.Proofs

noncomputable def euclideanInv : ℂ → ℂ := EuclideanGeometry.inversion 0 1

theorem euclideanInv_eq_star_inv (z : ℂ) : euclideanInv z = star (z⁻¹) := by
  by_cases hz : z = 0
  · simp [euclideanInv, hz, EuclideanGeometry.inversion]
  have hn := (norm_pos_iff.mpr hz).ne'
  rw [euclideanInv, EuclideanGeometry.inversion, dist_eq_norm]
  simp only [sub_zero, vadd_eq_add, add_zero]
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq]
  simp
  ring

theorem euclideanInv_measurable : Measurable euclideanInv := by
  rw [show euclideanInv = fun z => star (z⁻¹) by
    funext z
    exact euclideanInv_eq_star_inv z]
  fun_prop

theorem euclideanInv_involutive : Function.Involutive euclideanInv := by
  intro z
  exact EuclideanGeometry.inversion_involutive 0 (by norm_num) z

theorem euclideanInv_abs_det (x : ℂ) (hx : x ≠ 0) :
    |(fderiv ℝ euclideanInv x).det| = ‖x‖ ^ (-4 : ℝ) := by
  let K := ℝ ∙ x
  let R : ℂ →L[ℝ] ℂ := Kᗮ.reflection
  have hdim : Module.finrank ℝ Kᗮ = 1 := by
    dsimp [K]
    let _ : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by
      simp⟩
    exact Submodule.finrank_orthogonal_span_singleton hx
  have hsum := Submodule.finrank_add_finrank_orthogonal (K := Kᗮ)
  rw [hdim, Complex.finrank_real_complex] at hsum
  have hdimDouble : Module.finrank ℝ Kᗮᗮ = 1 := by omega
  have hdetR : R.det = -1 := by
    change LinearMap.det R.toLinearMap = -1
    rw [show R.toLinearMap = Kᗮ.reflection.toLinearEquiv.toLinearMap by rfl, Submodule.det_reflection, hdimDouble]
    norm_num
  have hfd : fderiv ℝ euclideanInv x = (‖x‖⁻¹) ^ 2 • R := by
    change fderiv ℝ (EuclideanGeometry.inversion 0 1) x = _
    rw [(EuclideanGeometry.hasFDerivAt_inversion (c := 0) (R := 1)
      (x := x) hx).fderiv]
    aesop
  rw [hfd]
  change |LinearMap.det (((‖x‖⁻¹) ^ 2 • R.toLinearMap))| = _
  rw [LinearMap.det_smul]
  have hdetR' : LinearMap.det R.toLinearMap = -1 := hdetR
  rw [hdetR', Complex.finrank_real_complex]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [abs_mul, abs_neg, abs_one, mul_one, abs_of_nonneg (by positivity)]
  calc
    ((‖x‖⁻¹) ^ 2) ^ 2 = (‖x‖⁻¹) ^ 4 := by linarith
    _ = (‖x‖ ^ 4)⁻¹ := by simp
    _ = ‖x‖ ^ (-4 : ℝ) := by
      rw [Real.rpow_neg hnorm.le]
      norm_num [Real.rpow_natCast]

noncomputable def refWeight (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (normPlus x ^ (-4 : ℝ))
section
variable (x : ℂ)

theorem normPlus_euclideanInv : normPlus (euclideanInv x) = normPlus x⁻¹ := by
  have hnorm : ‖euclideanInv x‖ = ‖x‖⁻¹ := by
    have h := EuclideanGeometry.dist_inversion_center 0 x 1
    aesop
  have hcomplex : ‖euclideanInv x‖ = ‖x⁻¹‖ := by
    simp_all
  unfold normPlus
  simp_all

theorem refWeight_jac (hx : x ≠ 0) :
    ENNReal.ofReal |(fderiv ℝ euclideanInv x).det| * refWeight (euclideanInv x) =
      refWeight x := by
  rw [euclideanInv_abs_det x hx, refWeight, refWeight, normPlus_euclideanInv x, ← ENNReal.ofReal_mul (by positivity : 0 ≤ ‖x‖ ^ (-4 : ℝ)), mul_comm, normPlus_inv_mul_jacobian hx]

end

theorem refWeight_measurable : Measurable refWeight := by
  change Measurable (fun x : ℂ => ENNReal.ofReal _)
  fun_prop [normPlus]

theorem euclideanInv_preimage_image_away (A : Set ℂ) :
    euclideanInv '' (A ∩ {x | x ≠ 0}) =
      euclideanInv ⁻¹' A ∩ {x | x ≠ 0} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    constructor
    · change euclideanInv (euclideanInv x) ∈ A
      simpa [euclideanInv_involutive x] using hx.1
    · intro hy0
      have hx0 : x = 0 := by
        have h := congrArg euclideanInv hy0
        rw [euclideanInv_involutive x, show euclideanInv 0 = 0 by
          simp [euclideanInv]] at h
        exact h
      simp_all
  · intro hy
    refine ⟨euclideanInv y, ?_, euclideanInv_involutive y⟩
    constructor
    · exact hy.1
    · intro hx0
      have h := congrArg euclideanInv hx0
      have hzeroI : euclideanInv 0 = 0 := by simp [euclideanInv]
      have hy0 : y = 0 := by
        rwa [euclideanInv_involutive y, hzeroI] at h
      simp_all

theorem euclideanInv_derivWithin_punctured (S : Set ℂ) (x : ℂ) (hx : x ≠ 0) :
    HasFDerivWithinAt euclideanInv (fderiv ℝ euclideanInv x) S x := by
  change HasFDerivWithinAt _
    (fderiv ℝ (EuclideanGeometry.inversion 0 1) x) S x
  rw [(EuclideanGeometry.hasFDerivAt_inversion
    hx).fderiv]
  exact (EuclideanGeometry.hasFDerivAt_inversion
    hx).hasFDerivWithinAt
section
variable (A : Set ℂ)
section
variable (hA : MeasurableSet A)
include hA

theorem refWeight_integral_euclideanInv_preimage_punctured :
    (∫⁻ x in euclideanInv ⁻¹' A ∩ {x | x ≠ 0}, refWeight x ∂volume) =
      (∫⁻ x in A ∩ {x | x ≠ 0}, refWeight x ∂volume) := by
  let S := A ∩ {x | x ≠ 0}
  have hS : MeasurableSet S := by measurability
  have hInj : Set.InjOn euclideanInv S := euclideanInv_involutive.injective.injOn
  have hderiv : ∀ x ∈ S,
      HasFDerivWithinAt euclideanInv (fderiv ℝ euclideanInv x) S x := by
    intro x hx
    exact euclideanInv_derivWithin_punctured S x hx.2
  have hchange := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) hS hderiv hInj refWeight
  rw [(euclideanInv_preimage_image_away A)] at hchange
  exact by
    calc
      _ = ∫⁻ x in S,
          ENNReal.ofReal |(fderiv ℝ euclideanInv x).det| * refWeight (euclideanInv x)
            ∂volume := hchange
      _ = ∫⁻ x in S, refWeight x ∂volume := by
        apply MeasureTheory.setLIntegral_congr_fun hS
        intro x hx
        exact refWeight_jac x hx.2

theorem gmcReferenceMeasure_euclideanInv_preimage :
    gmcReferenceMeasure (euclideanInv ⁻¹' A) = gmcReferenceMeasure A := by
  have hzero : ∀ᵐ x ∂volume, x ≠ (0 : ℂ) := by
    rw [ae_iff]
    simp
  have hAae : A =ᵐ[volume] A ∩ {x | x ≠ 0} := by
    filter_upwards [hzero] with x hx
    simp_all
  have hpreae : euclideanInv ⁻¹' A =ᵐ[volume]
      euclideanInv ⁻¹' A ∩ {x | x ≠ 0} := by
    filter_upwards [hzero] with x hx
    simp_all
  have hAres := Measure.restrict_congr_set hAae
  have hpreres := Measure.restrict_congr_set hpreae
  calc
    gmcReferenceMeasure _ =
        ∫⁻ x in euclideanInv ⁻¹' A, refWeight x ∂volume := by
          rw [gmcReferenceMeasure, withDensity_apply _
            (hA.preimage euclideanInv_measurable)]
          rfl
    _ = ∫⁻ x in euclideanInv ⁻¹' A ∩ {x | x ≠ 0}, refWeight x ∂volume := by
          simp_all
    _ = ∫⁻ x in A ∩ {x | x ≠ 0}, refWeight x ∂volume := (refWeight_integral_euclideanInv_preimage_punctured A hA)
    _ = ∫⁻ x in A, refWeight x ∂volume := by
          simp_all
    _ = gmcReferenceMeasure A := by
          rw [gmcReferenceMeasure, withDensity_apply _ hA]
          rfl

end

end

theorem gmcReferenceMeasure_map_euclideanInv :
    gmcReferenceMeasure.map euclideanInv = gmcReferenceMeasure := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply euclideanInv_measurable hA]
  exact gmcReferenceMeasure_euclideanInv_preimage A hA

theorem gmcReferenceMeasure_map_conj :
    gmcReferenceMeasure.map star = gmcReferenceMeasure := by
  let hstar : MeasurePreserving star volume volume :=
    Complex.conjLIE.measurePreserving
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hstar.measurable hA]
  change (volume.withDensity refWeight) _ =
    (volume.withDensity refWeight) A
  rw [withDensity_apply _ (hA.preimage hstar.measurable), withDensity_apply _ hA]
  have hrestrict :=
    hstar.restrict_preimage hA
  calc
    ∫⁻ x in star ⁻¹' A, refWeight x ∂volume =
        ∫⁻ x, refWeight (star x) ∂volume.restrict _ := by
          apply setLIntegral_congr_fun (hA.preimage hstar.measurable)
          intro x hx
          simp [refWeight, normPlus]
    _ = ∫⁻ x in A, refWeight x ∂volume := hrestrict.lintegral_comp refWeight_measurable

theorem gmcReferenceMeasure_map_complexInv :
    gmcReferenceMeasure.map (fun x : ℂ => x⁻¹) = gmcReferenceMeasure := by
  have hfun : (fun x : ℂ => x⁻¹) = star ∘ euclideanInv := by
    funext x
    simp [Function.comp_apply, euclideanInv_eq_star_inv]
  have hcomp : star ∘ euclideanInv =
      (⇑Complex.conjLIE) ∘ euclideanInv := by
    rfl
  rw [hfun, hcomp]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (Complex.conjLIE.measurePreserving.measurable.aemeasurable)
    (euclideanInv_measurable.aemeasurable)]
  rw [gmcReferenceMeasure_map_euclideanInv]
  have hstarEq : (⇑Complex.conjLIE) = star := by
    rfl
  rw [hstarEq, gmcReferenceMeasure_map_conj]

end DOZZ.Proofs
