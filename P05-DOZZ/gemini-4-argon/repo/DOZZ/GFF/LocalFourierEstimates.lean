/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusFourierEmbedding
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.Norm

/-!
# DOZZ.GFF.LocalFourierEstimates

Fourier integration by parts estimates for the scaled compactly supported tests in a torus box.
-/

@[expose] public section

open MeasureTheory
open Set Metric
open scoped FourierTransform InnerProductSpace Topology

namespace DOZZ

/-- Rescale a compactly supported test from a physical box to the unit square. -/
noncomputable def gffUnitBoxFunction (L : ℝ) (f : TestFn) : ℂ → ℝ :=
  fun z => f (L • z)



/-- The derivative of a smooth compactly supported complex function in a fixed direction is
compactly supported and smooth. -/
noncomputable def complexDirectionalDerivative (f : ℂ → ℂ) (v : ℂ) : ℂ → ℂ :=
  fun z => (fderiv ℝ f z) v

private theorem realInnerComplex_eq (z w : ℂ) :
    ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  simp [Complex.mul_re]
  ring




/-- A test function restricted to the unit square and scaled from a physical box of side `L`. -/
noncomputable def gffUnitBoxComplexFunction (L : ℝ) (f : TestFn) : ℂ → ℂ :=
  fun z => (gffUnitBoxFunction L f z : ℂ)




/-- A physical derivative rescaled by the box side so that it becomes a unit-box derivative. -/
noncomputable def unitBoxDirectionalDerivativeTest (L : ℝ) (f : TestFn) (v : ℂ) : TestFn :=
  L • directionalDerivativeTest f v

theorem support_unitBoxDirectionalDerivativeTest_subset (L R : ℝ) (f : TestFn)
    (v : ℂ) (hf : Function.support f ⊆ ball (0 : ℂ) R) :
    Function.support (unitBoxDirectionalDerivativeTest L f v) ⊆
      ball (0 : ℂ) (R + 1) := by
  have hderiv : Function.support (directionalDerivativeTest f v) ⊆ tsupport f := by
    calc
      Function.support (directionalDerivativeTest f v) ⊆
          tsupport (directionalDerivativeTest f v) := subset_tsupport _
      _ ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v
  intro z hz
  exact closedBall_subset_ball (by linarith) ((show tsupport f ⊆ closedBall (0 : ℂ) R by change closure (Function.support f) ⊆ closedBall (0 : ℂ) R; exact (closure_mono hf).trans closure_ball_subset_closedBall) (hderiv (by by_contra hn; apply hz; simp [unitBoxDirectionalDerivativeTest, (by simpa [Function.mem_support] using hn)])))



private def centeredUnitBox : Set (Fin 2 → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)}

private theorem measurableSet_centeredUnitBox : MeasurableSet centeredUnitBox := by
  have hEq : centeredUnitBox =
      ⋂ i : Fin 2, {x : Fin 2 → ℝ | x i ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)} := by
    ext x
    simp [centeredUnitBox]
    norm_num
  rw [hEq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Ioc.preimage (measurable_pi_apply (X := fun _ : Fin 2 => ℝ) i)

/-- A compactly supported function whose support lies in a measurable set has the same total
integral as its integral over that set. -/
private theorem integral_eq_setIntegral_of_support_subset_box {α : Type*}
    [MeasurableSpace α] [CompleteSpace ℂ] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {F : α → ℂ} (hF : Function.support F ⊆ s) :
    (∫ x, F x ∂μ) = ∫ x in s, F x ∂μ := by
  calc
    (∫ x, F x ∂μ) = ∫ x, s.indicator F x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ s
      · simp [hx]
      · have hzero : F x = 0 := by
          by_contra hn
          exact hx (hF hn)
        simp [hx, hzero]
    _ = ∫ x in s, F x ∂μ := by rw [integral_indicator (μ := μ) hs]


noncomputable def unitTorusFourierFrequency (k : Fin 2 → ℤ) : ℂ :=
  (k 0 : ℂ) + (k 1 : ℂ) * Complex.I


theorem unitTorusFourierFrequency_innerSL
    k (z : ℂ) :
    (innerSL ℝ) (unitTorusFourierFrequency k) z =
      z.re * (k 0 : ℝ) + z.im * (k 1 : ℝ) := by
  rw [innerSL_apply_apply, realInnerComplex_eq]
  simp [unitTorusFourierFrequency, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im] ; ring

private noncomputable def unitTorusFourierIntegrand
    (L : ℝ) (f : TestFn) (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I *
    ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) *
      gffUnitBoxComplexFunction L f (Complex.measurableEquivPi.symm x)



/-- A torus Fourier coefficient of a test supported inside the fundamental box is the ordinary
Fourier transform of its scaled compactly supported extension. -/
theorem torusPeriodizationCoeff_eq_fourier
    (L R : ℝ) (hL : 0 < L) (hRL : R < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
      𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) := by
  have support_unitTorusFourierIntegrand_subset_box : Function.support (unitTorusFourierIntegrand L f k) ⊆ centeredUnitBox := by
    have gffUnitBoxComplexFunction_support_subset_centeredBox : Function.support (gffUnitBoxComplexFunction L f) ⊆ {z : ℂ | z.re ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ) ∧ z.im ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)} := by
      intro z hz
      have hval : gffUnitBoxFunction L f z ≠ 0 := by
        intro hzero
        apply hz
        simp [gffUnitBoxComplexFunction, hzero]
      have hzball := hf (by change f (L • z) ≠ 0; exact_mod_cast hval)
      have hnorm : ‖L • z‖ < R := by
        simpa [Metric.mem_ball, dist_zero_right] using hzball
      have hnormz : ‖z‖ < R / L := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL] at hnorm
        apply (lt_div_iff₀ hL).2
        simpa [mul_comm] using hnorm
      have hsmall : R / L < 1 / 2 := by
        apply (div_lt_iff₀ hL).2
        nlinarith [hRL]
      have hre := (Complex.abs_re_le_norm z).trans_lt (hnormz.trans hsmall)
      have him := (Complex.abs_im_le_norm z).trans_lt (hnormz.trans hsmall)
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · linarith [abs_lt.mp hre]
      · linarith [abs_lt.mp hre]
      · linarith [abs_lt.mp him]
      · linarith [abs_lt.mp him]
    intro x hx
    have hscaled : gffUnitBoxComplexFunction L f
        (Complex.measurableEquivPi.symm x) ≠ 0 := by
      intro hzero
      apply hx
      have hzero' : gffUnitBoxComplexFunction L f
          (x 0 + x 1 * Complex.I) = 0 := by
        simpa only [Complex.measurableEquivPi_symm_apply] using hzero
      simp [unitTorusFourierIntegrand, hzero']
    have hz := hscaled
    rcases gffUnitBoxComplexFunction_support_subset_centeredBox hz with
      ⟨hre, him⟩
    change ∀ i : Fin 2, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)
    intro i
    fin_cases i
    · change x 0 ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)
      constructor
      · simpa [Complex.measurableEquivPi_symm_apply] using hre.1
      · have hupper : x 0 ≤ 1 / 2 := by
          simpa [Complex.measurableEquivPi_symm_apply] using hre.2
        norm_num at hupper ⊢
        linarith
    · change x 1 ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)
      constructor
      · simpa [Complex.measurableEquivPi_symm_apply] using him.1
      · have hupper : x 1 ≤ 1 / 2 := by
          simpa [Complex.measurableEquivPi_symm_apply] using him.2
        norm_num at hupper ⊢
        linarith
  have unitTorusFourierIntegrand_measurableEquivPi z : Complex.exp (↑(-2 * Real.pi * ((innerSL ℝ) z (unitTorusFourierFrequency k))) * Complex.I) * gffUnitBoxComplexFunction L f z = unitTorusFourierIntegrand L f k (Complex.measurableEquivPi z) := by
    have innerSL_unitTorusFourierFrequency (z : ℂ) k : (innerSL ℝ) z (unitTorusFourierFrequency k) = z.re * (k 0 : ℝ) + z.im * (k 1 : ℝ) := by
      rw [innerSL_apply_apply, realInnerComplex_eq]
      simp [unitTorusFourierFrequency, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im]
    unfold unitTorusFourierIntegrand
    rw [Complex.measurableEquivPi.symm_apply_apply z]
    congr 1
    rw [innerSL_unitTorusFourierFrequency]
    simp [Complex.measurableEquivPi_apply]
    ring_nf
  have unitTorus_mFourier_neg_eq_exp_dot k (x : Fin 2 → ℝ) : UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) = Complex.exp (-2 * Real.pi * Complex.I * ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) := by
    have unitTorus_mFourier_neg_eq_exp k (x : Fin 2 → ℝ) : UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) = Complex.exp (-2 * Real.pi * Complex.I * (k 0 : ℝ) * x 0) * Complex.exp (-2 * Real.pi * Complex.I * (k 1 : ℝ) * x 1) := by
      rw [UnitAddTorus.mFourier_neg]
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
        fourier_coe_apply]
      rw [map_mul, ← Complex.exp_conj, ← Complex.exp_conj]
      congr 1 <;> simp [map_mul, map_ofNat]
    rw [unitTorus_mFourier_neg_eq_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  let E := Complex.measurableEquivPi
  let H := unitTorusFourierIntegrand L f k
  calc
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
        ∫ x in centeredUnitBox,
          UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
            torusPeriodizationFunction L f (fun i => (x i : UnitAddCircle)) := by
      simpa [centeredUnitBox] using (torusPeriodizationCoeff_eq_boxIntegral L f k)
    _ = ∫ x in centeredUnitBox, H x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_centeredUnitBox] with x hx
      simp only [H, unitTorusFourierIntegrand, smul_eq_mul]
      rw [unitTorus_mFourier_neg_eq_exp_dot]
      congr 1
      have hpoint : Complex.equivRealProdCLM.symm (L * x 0, L * x 1) =
          L • Complex.measurableEquivPi.symm x := by
        rw [Complex.equivRealProdCLM_symm_apply, Complex.measurableEquivPi_symm_apply]
        apply Complex.ext
        · simp [Complex.real_smul]
        · simp [Complex.real_smul]
      rw [(show torusPeriodizationFunction L f (fun i => (x i : UnitAddCircle)) = ((f (Complex.equivRealProdCLM.symm (L * x 0, L * x 1)) : ℝ) : ℂ) by simpa using (torusPeriodizationFunction_rep L f ⟨x, (by simpa [centeredUnitBox] using hx)⟩)), hpoint]
      rfl
    _ = ∫ x, H x := by
      symm
      exact integral_eq_setIntegral_of_support_subset_box
        (μ := volume) measurableSet_centeredUnitBox (support_unitTorusFourierIntegrand_subset_box)
    _ = 𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) := by
      symm
      calc
        𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) =
            ∫ z, Complex.exp
              (↑(-2 * Real.pi * ((innerSL ℝ) z (unitTorusFourierFrequency k))) *
                Complex.I) * gffUnitBoxComplexFunction L f z := by
          rw [Real.fourier_eq']
          simp_rw [smul_eq_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          congr 1
        _ = ∫ z, H (E z) := by
          apply integral_congr_ae
          filter_upwards [] with z
          simpa [H, E] using
            unitTorusFourierIntegrand_measurableEquivPi z
        _ = ∫ x, H x := (Complex.volume_preserving_equiv_pi).integral_comp' H

/-- Differentiating a test in a physical coordinate multiplies its unit-torus Fourier
coefficient by the corresponding frequency. -/
theorem torusPeriodizationCoeff_unitBoxDirectionalDerivative
    (L R : ℝ) (hL : 0 < L) (hRbox : R + 1 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (v : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodizationLp L (unitBoxDirectionalDerivativeTest L f v)) k =
      (2 * Real.pi * Complex.I *
        ((innerSL ℝ) (unitTorusFourierFrequency k) v : ℂ)) *
        UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  have gffUnitBoxComplexFunction_unitBoxDirectionalDerivativeTest (hL : L ≠ 0) f v z : gffUnitBoxComplexFunction L (unitBoxDirectionalDerivativeTest L f v) z = complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
    have gffUnitBoxComplexFunction_directionalDerivative f v z : gffUnitBoxComplexFunction L (directionalDerivativeTest f v) z = (L : ℂ)⁻¹ * complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
      have hderiv :
          fderiv ℝ (fun y => ((f (L • y) : ℝ) : ℂ)) z =
            (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp
              (L • fderiv ℝ (f : ℂ → ℝ) (L • z)) := by
        change fderiv ℝ (Complex.ofReal ∘ (fun y : ℂ => f (L • y))) z = _
        rw [fderiv_comp]
        · rw [show fderiv ℝ Complex.ofReal (f (L • z)) = Complex.ofRealCLM from by
              change fderiv ℝ (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) _ = _
              exact ContinuousLinearMap.fderiv _]
          rw [fderiv_comp_smul]
        · exact Complex.differentiable_ofReal.differentiableAt
        · exact (f.contDiff.differentiable (by simp)).differentiableAt.comp z
            (by fun_prop)
      change ((fderiv ℝ (f : ℂ → ℝ) (L • z)) v : ℂ) =
        (L : ℂ)⁻¹ * (fderiv ℝ (gffUnitBoxComplexFunction L f) z) v
      rw [show fderiv ℝ (gffUnitBoxComplexFunction L f) z =
          fderiv ℝ (fun y => ((f (L • y) : ℝ) : ℂ)) z by rfl, hderiv]
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        smul_eq_mul, Complex.real_smul, Complex.ofRealCLM_apply]
      field_simp [(by exact_mod_cast hL)]
      rw [← Complex.ofReal_mul]
    rw [unitBoxDirectionalDerivativeTest]
    calc
      gffUnitBoxComplexFunction L (L • directionalDerivativeTest f v) z =
          (L : ℂ) * gffUnitBoxComplexFunction L (directionalDerivativeTest f v) z := by
        simp [gffUnitBoxComplexFunction, gffUnitBoxFunction, Complex.real_smul]
      _ = complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
        rw [gffUnitBoxComplexFunction_directionalDerivative]
        field_simp [(by exact_mod_cast hL)]
  have gffUnitBoxComplexFunction_hasCompactSupport (hL : L ≠ 0) f : HasCompactSupport (gffUnitBoxComplexFunction L f) := by
    have gffUnitBoxFunction_hasCompactSupport : HasCompactSupport (gffUnitBoxFunction L f) := by
      exact f.hasCompactSupport.comp_smul hL
    apply (gffUnitBoxFunction_hasCompactSupport).mono
    intro z hz
    change ((gffUnitBoxFunction L f z : ℝ) : ℂ) ≠ 0 at hz
    intro hzero
    apply hz
    exact_mod_cast hzero
  have fourier_complexDirectionalDerivative {f : ℂ → ℂ} (hf : ContDiff ℝ (↑(⊤ : ENat)) f) (hcompact : HasCompactSupport f) (v : ℂ) (w : ℂ) : 𝓕 (complexDirectionalDerivative f v) w = (2 * Real.pi * Complex.I * ((innerSL ℝ) w v : ℂ)) * 𝓕 f w := by
    have hdfint : Integrable (fun z => fderiv ℝ f z) := ((contDiffOn_univ.mp ((contDiffOn_univ.mpr hf).fderiv_of_isOpen isOpen_univ (by simp) : ContDiffOn ℝ (↑(⊤ : ENat)) (fderiv ℝ f) Set.univ)).continuous).integrable_of_hasCompactSupport (hcompact.fderiv (𝕜 := ℝ))
    have happly := congrArg (fun T : ℂ →L[ℝ] ℂ => T v) (congrFun (Real.fourier_fderiv (E := ℂ) ((hf.continuous.integrable_of_hasCompactSupport hcompact)) (hf.differentiable (by simp)) hdfint) w)
    rw [Real.fourier_continuousLinearMap_apply hdfint] at happly
    have hcoords : (innerSL ℝ) w v = w.re * v.re + w.im * v.im := by
      rw [innerSL_apply_apply, realInnerComplex_eq]
    simp only [VectorFourier.fourierSMulRight_apply, neg_apply,
      smul_eq_mul] at happly
    rw [hcoords] at happly
    rw [Complex.real_smul] at happly
    rw [hcoords]
    convert happly using 1
    · rfl
    · push_cast
      ring
  rw [torusPeriodizationCoeff_eq_fourier L (R + 1) hL hRbox
    (unitBoxDirectionalDerivativeTest L f v) (support_unitBoxDirectionalDerivativeTest_subset L R f v hf) k]
  rw [(show gffUnitBoxComplexFunction L (unitBoxDirectionalDerivativeTest L f v) = complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v by funext z; exact gffUnitBoxComplexFunction_unitBoxDirectionalDerivativeTest (ne_of_gt hL) f v z)]
  rw [fourier_complexDirectionalDerivative
    ((by unfold gffUnitBoxComplexFunction; exact Complex.ofRealCLM.contDiff.comp ((show ContDiff ℝ (↑(⊤ : ENat)) (gffUnitBoxFunction L f) by unfold gffUnitBoxFunction; exact f.contDiff.comp (contDiff_const_smul L)))))
    (gffUnitBoxComplexFunction_hasCompactSupport (ne_of_gt hL) f)
    v (unitTorusFourierFrequency k)]
  rw [← torusPeriodizationCoeff_eq_fourier L (R + 1) hL hRbox f (hf.trans (ball_subset_ball (by linarith))) k]

/-- Two unit-box derivatives multiply the torus coefficient by the squared frequency. -/
theorem torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
    (L R : ℝ) (hL : 0 < L) (hRbox : R + 2 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (v : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodizationLp L
          (unitBoxDirectionalDerivativeTest L
            (unitBoxDirectionalDerivativeTest L f v) v)) k =
      (2 * Real.pi * Complex.I *
        ((innerSL ℝ) (unitTorusFourierFrequency k) v : ℂ)) ^ 2 *
        UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  rw [(torusPeriodizationCoeff_unitBoxDirectionalDerivative L (R + 1) hL (by linarith) (unitBoxDirectionalDerivativeTest L f v) (support_unitBoxDirectionalDerivativeTest_subset L R f v hf) v k), (torusPeriodizationCoeff_unitBoxDirectionalDerivative L R hL (by linarith) f hf v k)]
  ring

end DOZZ

end
