/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourcePolarFinite
public import DOZZ.FourPoint.Dual.SourceCopiedKernelSqueeze
public import DOZZ.FourPoint.Dual.KernelInverseExpectation
public import DOZZ.FourPoint.Dual.CopiedInverseTriple
public import DOZZ.FourPoint.Dual.OuterInverseTransport
public import DOZZ.FourPoint.Dual.SourceRadialMoments
import Mathlib.Tactic
public import DOZZ.GFFStructure.ContinuousCircleAverage
public import DOZZ.MeasureTheory.FiniteOnChart
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
/-! The actual copied kernel inverse expectation is controlled by the same-source polar loss. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- All measurability, positivity, inverse integrability and polar finiteness inputs to the
copied-kernel relative error are discharged on the supplied source and common plane carrier. -/
theorem dual_source_copied_kernel_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hcircle : IsContinuousCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω))
    (heN : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (heZ : Z =ᵐ[P] (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (α₁ α₂ α₃ ξ h p : ℝ) (hp : 0 < p) (hh : 0 < h)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hznorm : ‖z‖ ≤ 1)
    (hz : ‖z‖ < ‖z‖^(1-ξ)) (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h)
    (hη : Real.exp (-(T : ℝ)) < 1)
    (hr : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ))
    (hiZ : IndepFun (originRadialPath Xc) Z P)
    (B : Ω → BrownianPath × BrownianPath) (Z₀ : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z₀)
    (hlaw : P.map (fun ω => (originRadialPath Xc ω,dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)) =
      (P.prod P).map (fun ω : Ω × Ω => (originRadialPath Xc ω.1,
        ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
          ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))) :
    let A := originRadialPath Xc
    let η := Real.exp (-(T : ℝ))
    let R := Real.exp (-h)
    let θlo := (1-R)^(2 : ℝ)*(1-η)⁻¹^(-|γ*α₂|)
    let θhi := (1+R)^(2 : ℝ)*(1-η)⁻¹^|γ*α₂|
    let O := fun v : Ω × Ω => ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ (A v.1) x) ∂N v.2
    let D := ∫ v : (Ω × Ω) × Ω,
      ((O v.1).toReal+dualPathRadialScale γ (Q γ-α₁) h z (A v.1.1)*
        (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
          (brownianShiftPath T (radialPositiveHalf (A v.1.1)) (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
            ∂(Z v.2).map (fun s => s-(T : ℝ))).toReal)^(-p)-(O v.1).toReal^(-p)
        ∂(P.prod P).prod P
    |(dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ p z η (‖z‖^(1-ξ))).toReal-
      (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal-D| ≤
      max |θlo-1| |θhi-1| * (-D) := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let η := Real.exp (-(T : ℝ))
  let R := Real.exp (-h)
  let θlo := (1-R)^(2 : ℝ)*(1-η)⁻¹^(-|γ*α₂|)
  let θhi := (1+R)^(2 : ℝ)*(1-η)⁻¹^|γ*α₂|
  let J := fun U (a : TwoSidedPath) ω => ∫⁻ x in U,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
  let O₀ := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let O := fun v : Ω × Ω => J (reflected_outerRegion (‖z‖^(1-ξ))) (A v.1) v.2
  let I := fun v : (Ω × Ω) × Ω => J (reflected_innerRegion η) (A v.1.1) v.2
  let β := fun v : (Ω × Ω) × Ω => dualPathRadialScale γ (Q γ-α₁) h z (A v.1.1)
  let V := fun v : (Ω × Ω) × Ω => ∫⁻ t,
    (if 0 < t then ENNReal.ofReal (Real.exp (γ*
      (brownianShiftPath T (radialPositiveHalf (A v.1.1)) (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
        ∂(Z v.2).map (fun s => s-(T : ℝ))
  let QP := (P.prod P).prod P
  have hA := originRadialPath_aemeasurable P X Xc hcircle.isCircleAverage hcircle.continuous_ae
  have hm {W : Set ℂ} (hW : IsOpen W) (hW0 : W ⊆ ({0} : Set ℂ)ᶜ) :
      Measurable (fun v : TwoSidedPath × Ω => J W v.1 v.2) :=
    reflected_reinserted_region_measurable hNm hfin γ hW.measurableSet hW0
      (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hi := hm (reflected_innerRegion_open η) (reflected_innerRegion_punctured _)
  have ho := hm (reflected_outerRegion_open (‖z‖ ^ (1 - ξ))) (reflected_outerRegion_punctured _)
  have hOm : AEMeasurable O (P.prod P) :=
    ho.comp_aemeasurable (hA.comp_fst.prodMk measurable_snd.aemeasurable)
  have hIm : AEMeasurable I QP := hi.comp_aemeasurable
    (hA.comp_fst.comp_fst.prodMk measurable_snd.aemeasurable)
  have hβm : AEMeasurable β QP :=
    (dual_path_radial_scale_measurable γ (Q γ-α₁) h z).comp_aemeasurable hA.comp_fst.comp_fst
  have hβpos : ∀ᵐ v ∂QP, 0 ≤ β v := ae_of_all _ (fun v => (Real.exp_pos _).le)
  have hO₀m : AEMeasurable O₀ P := (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hrnorm : ‖z‖^(1-ξ) ≤ 1 := by
    simpa using Real.rpow_le_rpow (norm_nonneg z) hznorm
          (sub_nonneg.mpr hξ1.le)
  have hO₀pos : ∀ᵐ ω ∂P, 0 < (O₀ ω).toReal :=
    (dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hznorm hrnorm).mono
      (fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne)
  have hO₀int : Integrable (fun ω => (O₀ ω).toReal^(-p)) P := by
    have ht := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hcircle.isCircleAverage
      (Q γ-α₁) h 0 α₁ α₂ α₃ ξ p hh.le hξ hξ1 hp.le z hz0 hznorm).1
    simpa only [Real.rpow_zero, one_mul] using ht
  have hdata := dual_joint_law_outer_inverse_data P (P.prod P) A (fun v => A v.1) O₀ O
    hA hA.comp_fst hO₀m hOm hlaw p hO₀pos hO₀int
  have hOpos : ∀ᵐ v ∂QP, 0 < (O v.1).toReal :=
    measurePreserving_fst.quasiMeasurePreserving.ae hdata.1
  obtain ⟨C, _, hC⟩ := dual_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ p hp.le
  have hInv₀ : (∫⁻ ω, O₀ ω^(-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hC z ξ hznorm hrnorm)
  have hInvEq := dual_joint_law_outer_inverse_lintegral P (P.prod P) A (fun v => A v.1)
    O₀ O hA hA.comp_fst hO₀m hOm hlaw p
  have hInv : (∫⁻ v : (Ω × Ω) × Ω, O v.1^(-p) ∂QP) ≠ ⊤ := by
    rw [lintegral_prod _ (hOm.comp_fst.pow_const (-p))]
    simp only [lintegral_const, measure_univ, mul_one]
    rw [← hInvEq]
    exact hInv₀
  have hDm : Measurable (fun a : TwoSidedPath => brownianShiftPath T (radialPositiveHalf a)) :=
    continuous_brownianShiftPath.measurable.comp
      (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hVm : AEMeasurable V QP := reflected_translated_polar_aemeasurable (P.prod P) P
    (fun v => brownianShiftPath T (radialPositiveHalf (A v.1))) (hDm.comp_aemeasurable hA.comp_fst)
    Z hZ.2.2.2.1 hZ.2.2.2.2.1 γ (Q γ-α₁) T
  have hVfin : ∀ᵐ v ∂QP, V v ≠ ⊤ :=
    (measurePreserving_fst.prod (MeasurePreserving.id P)).quasiMeasurePreserving.ae
      (dual_source_restarted_polar_finite_ae P X Xc hX hcircle γ hγ hγ₂ M hM
        h α₁ α₂ α₃ ξ hα₁ z hz0 hz T hT hr Z hZ hiZ B Z₀ hData)
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hR1 : R < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hh)
  have hηEq : η = R*‖z‖ := by
    dsimp only [η, R]
    rw [hT]
    have he : -(-Real.log ‖z‖+h) = -h+Real.log ‖z‖ := by ring
    rw [he, Real.exp_add, Real.exp_log (norm_pos_iff.mpr hz0)]
  have hθlo : 0 ≤ θlo := mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hR1.le) _)
    (Real.rpow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hη.le)) _)
  have hθhi : 0 ≤ θhi := mul_nonneg (Real.rpow_nonneg (by linarith only [hR0]) _)
    (Real.rpow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hη.le)) _)
  have hs : ∀ᵐ v ∂QP, ENNReal.ofReal (θlo*β v)*V v ≤ I v ∧ I v ≤ ENNReal.ofReal (θhi*β v)*V v := by
    have ht := dual_source_copied_inner_kernel_squeeze P γ α₁ α₂ α₃ h R hγ.ne'
      A M N Z heN heZ z hz0 T hT hR0 hR1 hη hηEq.le
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae ht] with v hv
    exact hv (A v.1.1)
  have hb := dual_ennreal_kernel_inverse_expectation_error QP (fun v => O v.1) I V β p θlo θhi
    hp hθlo hθhi hOm.comp_fst hIm hVm hβm hβpos hOpos hVfin hInv hs
  have hCopy := dual_copied_inverse_moment_triple P Xc hA N hNm hfin γ α₁ α₂ α₃ p η (‖z‖^(1-ξ)) z
  have hCopy' : dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ p z η (‖z‖^(1-ξ)) =
      ∫⁻ v : (Ω × Ω) × Ω, (O v.1+I v)^(-p) ∂QP := by
    rw [hCopy]
    apply lintegral_congr
    intro v
    exact congrArg (fun a : ℝ≥0∞ => a^(-p)) (add_comm _ _)
  have hInvEq' : (∫⁻ v : (Ω × Ω) × Ω, O v.1^(-p) ∂QP) = ∫⁻ ω, O₀ ω^(-p) ∂P := by
    rw [lintegral_prod _ (hOm.comp_fst.pow_const (-p))]
    simp only [lintegral_const, measure_univ, mul_one]
    exact hInvEq.symm
  rw [← hCopy', hInvEq'] at hb
  have hLoss : (∫ v : (Ω × Ω) × Ω, (O v.1).toReal^(-p)-
      ((O v.1).toReal+β v*(V v).toReal)^(-p) ∂QP) =
      -(∫ v : (Ω × Ω) × Ω, ((O v.1).toReal+β v*(V v).toReal)^(-p)-
        (O v.1).toReal^(-p) ∂QP) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by ring)
  rw [hLoss] at hb
  exact hb

end DOZZ.Proofs
