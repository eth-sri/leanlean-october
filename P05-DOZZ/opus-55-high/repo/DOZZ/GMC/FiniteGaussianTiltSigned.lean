/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GMC.FiniteGaussianTilt

/-! Signed finite tilting follows from positive tilting and integrability. -/

public section

open MeasureTheory ProbabilityTheory ENNReal
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private lemma ennreal_ofReal_max_zero (x : ℝ) :
    ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  simp

/-- Signed finite-dimensional Cameron--Martin tilt, derived by applying the nonnegative identity
to the positive and negative parts. -/
theorem finite_gaussian_tilt_signed
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (a : ι → ℝ)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (hI : Integrable (fun ω => F (fun i => Z ω i +
      ∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j)) P) :
    ∫ ω, Real.exp ((∑ i, a i * Z ω i) -
        (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P (fun ω => Z ω i)
          (fun ω => Z ω j) * a j) / 2) * F (Z ω) ∂P =
      ∫ ω, F (fun i => Z ω i +
        ∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) ∂P := by
  let shift : (ι → ℝ) → (ι → ℝ) := fun y i => y i +
    ∑ j, DOZZ.gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j
  let tiltExp : Ω → ℝ := fun ω => Real.exp ((∑ i, a i * Z ω i) -
    (∑ i, ∑ j, a i * DOZZ.gaussianCovariance P (fun ω => Z ω i)
      (fun ω => Z ω j) * a j) / 2)
  let G : Ω → ℝ := fun ω => tiltExp ω * F (Z ω)
  let pos : (ι → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (max (F y) 0)
  let neg : (ι → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (max (-F y) 0)
  let absF : (ι → ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal (|F y|)
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro i
    exact hZ.2.1 i
  have hFZ := hF.aemeasurable.comp_aemeasurable hZae
  have hlinAE : AEMeasurable (fun ω => ∑ i, a i * Z ω i) P := by
    fun_prop
  have hTiltExp : AEMeasurable tiltExp P := by
    fun_prop
  have hGmeas : AEStronglyMeasurable G P := by
    fun_prop
  have hPosMeas : Measurable pos := by
    fun_prop
  have hNegMeas : Measurable neg := by
    fun_prop
  have hAbsMeas : Measurable absF := by
    fun_prop
  have hAbsTilt := finite_gaussian_tilt P Z hZ a absF hAbsMeas
  have hIShift : Integrable (fun ω => F (shift (Z ω))) P := by
    simpa [shift] using hI
  have hAbsShift := hIShift.norm
  have hAbsShiftFinite :
      ∫⁻ ω, ENNReal.ofReal (|F (shift (Z ω))|) ∂P ≠ ∞ := (lintegral_ofReal_ne_top_iff_integrable
      hAbsShift.aestronglyMeasurable (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).2
      hAbsShift
  have hNormGFinite : ∫⁻ ω, ENNReal.ofReal (‖G ω‖) ∂P ≠ ∞ := by
    have hAbsG (ω : Ω) : |G ω| = tiltExp ω * |F (Z ω)| := by
      rw [show G ω = tiltExp ω * F (Z ω) by rfl, abs_mul,
        abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    have hpoint (ω : Ω) : ENNReal.ofReal (‖G ω‖) =
        ENNReal.ofReal (tiltExp ω) * absF (Z ω) := by
      calc
        ENNReal.ofReal (‖G ω‖) = ENNReal.ofReal (|G ω|) := by simp
        _ = ENNReal.ofReal (tiltExp ω * |F (Z ω)|) := by simp_all
        _ = ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (|F (Z ω)|) :=
          ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))
        _ = ENNReal.ofReal (tiltExp ω) * absF (Z ω) := rfl
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (tiltExp ω) * absF (Z ω) ∂P := by
        apply lintegral_congr_ae
        exact ae_of_all _ hpoint
      _ = ∫⁻ ω, absF (shift (Z ω)) ∂P := hAbsTilt
      _ = ∫⁻ ω, ENNReal.ofReal (|F (shift (Z ω))|) ∂P := by
        apply lintegral_congr_ae
        exact ae_of_all _ (fun ω => by rfl)
      _ ≠ ∞ := hAbsShiftFinite
  have hGInt : Integrable G P := by
    rw [← integrable_norm_iff hGmeas]
    exact (lintegral_ofReal_ne_top_iff_integrable hGmeas.norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).mp hNormGFinite
  have hLeftPos :
    ∫⁻ ω, ENNReal.ofReal (G ω) ∂P =
        ∫⁻ ω, ENNReal.ofReal (tiltExp ω) * pos (Z ω) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      change ENNReal.ofReal (G ω) = _
      rw [show G ω = tiltExp ω * F (Z ω) by rfl,
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      change ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (F (Z ω)) =
        ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal (max (F (Z ω)) 0)
      rw [ennreal_ofReal_max_zero])
  have hLeftNeg :
    ∫⁻ ω, ENNReal.ofReal (-G ω) ∂P =
        ∫⁻ ω, ENNReal.ofReal (tiltExp ω) * neg (Z ω) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      change ENNReal.ofReal (-G ω) = _
      rw [show -G ω = tiltExp ω * (-F (Z ω)) by linarith,
        ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
      change ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal _ =
        ENNReal.ofReal (tiltExp ω) * ENNReal.ofReal _
      rw [ennreal_ofReal_max_zero])
  have hRightPos :
    ∫⁻ ω, pos (shift (Z ω)) ∂P =
        ∫⁻ ω, ENNReal.ofReal (F (shift (Z ω))) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      exact ennreal_ofReal_max_zero _)
  have hRightNeg :
    ∫⁻ ω, neg (shift (Z ω)) ∂P =
        ∫⁻ ω, ENNReal.ofReal (-F (shift (Z ω))) ∂P := by
    apply lintegral_congr_ae
    exact ae_of_all _ (fun ω => by
      exact ennreal_ofReal_max_zero _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hGInt,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIShift,
    hLeftPos, hLeftNeg, (finite_gaussian_tilt P Z hZ a pos hPosMeas), (finite_gaussian_tilt P Z hZ a neg hNegMeas), hRightPos, hRightNeg]

end DOZZ.Proofs
