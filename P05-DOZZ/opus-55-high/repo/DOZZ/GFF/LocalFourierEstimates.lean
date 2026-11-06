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
section
variable (L : ℝ)

theorem gffUnitBoxFunction_contDiff (f : TestFn) :
    ContDiff ℝ (↑(⊤ : ENat)) (gffUnitBoxFunction L f) := by
  exact f.contDiff.comp (contDiff_const_smul L)

theorem gffUnitBoxFunction_hasCompactSupport (hL : L ≠ 0) (f : TestFn) :
    HasCompactSupport (gffUnitBoxFunction L f) := f.hasCompactSupport.comp_smul hL

end

/-- The derivative of a smooth compactly supported complex function in a fixed direction is
compactly supported and smooth. -/
noncomputable def complexDirectionalDerivative (f : ℂ → ℂ) (v : ℂ) : ℂ → ℂ :=
  fun z => (fderiv ℝ f z) v

private theorem realInnerComplex_eq (z w : ℂ) :
    ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  simp [Complex.mul_re]
  ring
section
variable {f : ℂ → ℂ}
section
variable (hf : ContDiff ℝ (↑(⊤ : ENat)) f) (hcompact : HasCompactSupport f)
include hf hcompact

private theorem complexFourier_integrable : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hcompact

/-- Integration by parts for the Fourier integral in a fixed direction. -/
theorem fourier_complexDirectionalDerivative (v w : ℂ) :
    𝓕 (complexDirectionalDerivative f v) w =
      (2 * Real.pi * Complex.I * ((innerSL ℝ) w v : ℂ)) * 𝓕 f w := by
  let df : ℂ → ℂ →L[ℝ] ℂ := fun z => fderiv ℝ f z
  have hdfOn : ContDiffOn ℝ (↑(⊤ : ENat)) (fderiv ℝ f) Set.univ :=
    by fun_prop
  have hdfint : Integrable df := ((contDiffOn_univ.mp hdfOn).continuous).integrable_of_hasCompactSupport (hcompact.fderiv (𝕜 := ℝ))
  have hdiff := hf.differentiable (by simp)
  have htransform := Real.fourier_fderiv (complexFourier_integrable hf hcompact) hdiff hdfint
  have happly := congrArg (fun T => T v) (congrFun htransform w)
  rw [Real.fourier_continuousLinearMap_apply hdfint] at happly
  have hcoords : (innerSL ℝ) w v = w.re * v.re + w.im * v.im := by
    rw [innerSL_apply_apply, realInnerComplex_eq]
  simp only [VectorFourier.fourierSMulRight_apply, neg_apply,
    smul_eq_mul] at happly
  rw [hcoords, Complex.real_smul] at happly
  rw [hcoords]
  convert happly using 1
  · rfl
  · push_cast
    ring

end

end

/-- The real two-torus monomial is the ordinary Euclidean Fourier character on its representative
square. -/
private theorem unitTorus_mFourier_neg_eq_exp (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (-2 * Real.pi * Complex.I * (k 0 : ℝ) * x 0) *
        Complex.exp (-2 * Real.pi * Complex.I * (k 1 : ℝ) * x 1) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply]
  congr 1 <;> simp [map_ofNat]

/-- A test function restricted to the unit square and scaled from a physical box of side `L`. -/
noncomputable def gffUnitBoxComplexFunction (L : ℝ) (f : TestFn) : ℂ → ℂ :=
  fun z => (gffUnitBoxFunction L f z : ℂ)
section
variable (L : ℝ)

theorem gffUnitBoxComplexFunction_contDiff (f : TestFn) :
    ContDiff ℝ (↑(⊤ : ENat)) (gffUnitBoxComplexFunction L f) := by
  exact Complex.ofRealCLM.contDiff.comp (gffUnitBoxFunction_contDiff L f)
section
variable (hL : L ≠ 0) (f : TestFn)
include hL

theorem gffUnitBoxComplexFunction_hasCompactSupport : HasCompactSupport (gffUnitBoxComplexFunction L f) := by
  apply (gffUnitBoxFunction_hasCompactSupport L hL f).mono
  intro z hz
  change ((gffUnitBoxFunction L f z : ℝ) : ℂ) ≠ 0 at hz
  simp_all

/-- Scaling a physical directional derivative back to the unit box contributes the expected
factor `L⁻¹`. -/
theorem gffUnitBoxComplexFunction_directionalDerivative (v z : ℂ) :
    gffUnitBoxComplexFunction L (directionalDerivativeTest f v) z =
      (L : ℂ)⁻¹ * complexDirectionalDerivative
        (gffUnitBoxComplexFunction L f) v z := by
  have hderiv :
      fderiv ℝ (fun y => ((f (L • y) : ℝ) : ℂ)) z =
        (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp
          (L • fderiv ℝ (f : ℂ → ℝ) (L • z)) := by
    change fderiv ℝ (Complex.ofReal ∘ (fun y : ℂ => f _)) z = _
    rw [fderiv_comp]
    · rw [show fderiv ℝ Complex.ofReal (f (L • z)) = Complex.ofRealCLM from by
          change fderiv ℝ (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) _ = _
          simp]
      rw [fderiv_comp_smul]
    · exact Complex.differentiable_ofReal.differentiableAt
    · exact (f.contDiff.differentiable (by simp)).differentiableAt.comp z
        (by fun_prop)
  change ((fderiv ℝ (f : ℂ → ℝ) _) v : ℂ) =
    (L : ℂ)⁻¹ * (fderiv ℝ _ z) v
  rw [show fderiv ℝ (gffUnitBoxComplexFunction L f) z =
      fderiv ℝ (fun y => ((f _ : ℝ) : ℂ)) z by rfl, hderiv]
  simp_all

end

end

/-- A physical derivative rescaled by the box side so that it becomes a unit-box derivative. -/
noncomputable def unitBoxDirectionalDerivativeTest (L : ℝ) (f : TestFn) (v : ℂ) : TestFn :=
  L • directionalDerivativeTest f v

theorem support_unitBoxDirectionalDerivativeTest_subset (L R : ℝ) (f : TestFn)
    (v : ℂ) (hf : Function.support f ⊆ ball (0 : ℂ) R) :
    Function.support (unitBoxDirectionalDerivativeTest L f v) ⊆
      ball (0 : ℂ) (R + 1) := by
  have htsupp : tsupport f ⊆ closedBall 0 R := by
    change closure (Function.support f) ⊆ closedBall 0 R
    exact (closure_mono hf).trans closure_ball_subset_closedBall
  have hderiv : Function.support (directionalDerivativeTest f v) ⊆ tsupport f := by
    calc
      Function.support _ ⊆
          tsupport _ := subset_tsupport _
      _ ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v
  intro z hz
  have hz' : z ∈ Function.support (directionalDerivativeTest f v) := by
    by_contra hn
    have hzero : directionalDerivativeTest f v z = 0 := by
      simp_all
    apply hz
    simp [unitBoxDirectionalDerivativeTest, hzero]
  exact closedBall_subset_ball (by linarith) (htsupp (hderiv hz'))

theorem gffUnitBoxComplexFunction_unitBoxDirectionalDerivativeTest
    (L : ℝ) (hL : L ≠ 0) (f : TestFn) (v z : ℂ) :
    gffUnitBoxComplexFunction L (unitBoxDirectionalDerivativeTest L f v) z =
      complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
  calc
    gffUnitBoxComplexFunction L (L • directionalDerivativeTest f v) z =
        L * gffUnitBoxComplexFunction L (directionalDerivativeTest f v) z := by
      simp [gffUnitBoxComplexFunction, gffUnitBoxFunction, Complex.real_smul]
    _ = complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
      rw [gffUnitBoxComplexFunction_directionalDerivative L hL]
      simp_all

/-- If a physical test is supported in a ball strictly smaller than half the box width, its
scaled representative is supported inside the centered fundamental square. -/
theorem gffUnitBoxComplexFunction_support_subset_centeredBox
    (L R : ℝ) (hL : 0 < L) (hRL : R < L / 2)
    (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) R) :
    Function.support (gffUnitBoxComplexFunction L f) ⊆
      {z : ℂ | z.re ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ) ∧
        z.im ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)} := by
  intro z hz
  have hval : gffUnitBoxFunction L f z ≠ 0 := by
    intro hzero
    apply hz
    simp [gffUnitBoxComplexFunction, hzero]
  have hscaled : L • z ∈ Function.support f := by
    assumption
  have hzball := hf hscaled
  have hnorm : ‖L • z‖ < R := by
    simp_all
  have hnormz : ‖z‖ < R / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL] at hnorm
    apply (lt_div_iff₀ hL).2
    linarith
  have hsmall : R / L < 1 / 2 := by
    apply (div_lt_iff₀ hL).2
    nlinarith
  have hre : |z.re| < 1 / 2 := (Complex.abs_re_le_norm z).trans_lt (hnormz.trans hsmall)
  have him : |z.im| < 1 / 2 := (Complex.abs_im_le_norm z).trans_lt (hnormz.trans hsmall)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> grind

private def centeredUnitBox : Set (Fin 2 → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)}

private theorem measurableSet_centeredUnitBox : MeasurableSet centeredUnitBox := by
  have hEq : centeredUnitBox =
      ⋂ i : Fin 2, {x : Fin 2 → ℝ | x i ∈ Set.Ioc (-1 / 2) (1 / 2)} := by
    ext x
    simp [centeredUnitBox]
    norm_num
  measurability

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
      · simp_all
      · have hzero : F x = 0 := by
          by_contra hn
          simp_all
        simp_all
    _ = ∫ x in s, F x ∂μ := by rw [integral_indicator hs]

private theorem unitTorus_mFourier_neg_eq_exp_dot
    (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (-2 * Real.pi * Complex.I *
        ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) := by
  rw [unitTorus_mFourier_neg_eq_exp, ← Complex.exp_add]
  ring

noncomputable def unitTorusFourierFrequency (k : Fin 2 → ℤ) : ℂ :=
  (k 0 : ℂ) + (k 1 : ℂ) * Complex.I

theorem innerSL_unitTorusFourierFrequency
    (z : ℂ) (k : Fin 2 → ℤ) :
    (innerSL ℝ) z (unitTorusFourierFrequency k) =
      z.re * (k 0 : ℝ) + z.im * (k 1 : ℝ) := by
  rw [innerSL_apply_apply, realInnerComplex_eq]
  simp [unitTorusFourierFrequency, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]

theorem unitTorusFourierFrequency_innerSL
    (k : Fin 2 → ℤ) (z : ℂ) :
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

private theorem unitTorusFourierIntegrand_measurableEquivPi
    (L : ℝ) (f : TestFn) (k : Fin 2 → ℤ) (z : ℂ) :
      Complex.exp
        (↑(-2 * Real.pi * ((innerSL ℝ) z (unitTorusFourierFrequency k))) *
          Complex.I) * gffUnitBoxComplexFunction L f z =
      unitTorusFourierIntegrand L f k (Complex.measurableEquivPi z) := by
  unfold unitTorusFourierIntegrand
  rw [Complex.measurableEquivPi.symm_apply_apply z]
  congr 1
  rw [innerSL_unitTorusFourierFrequency]
  simp [Complex.measurableEquivPi_apply]
  ring_nf
section
variable (L R : ℝ)
section
variable (hL : 0 < L) (hRL : R < L / 2) (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) R) (k : Fin 2 → ℤ)
include hL hRL hf

private theorem support_unitTorusFourierIntegrand_subset_box
    :
    Function.support (unitTorusFourierIntegrand L f k) ⊆ centeredUnitBox := by
  intro x hx
  have hscaled : gffUnitBoxComplexFunction L f
      (Complex.measurableEquivPi.symm x) ≠ 0 := by
    intro hzero
    apply hx
    have hzero' : gffUnitBoxComplexFunction L f
        (x 0 + x 1 * Complex.I) = 0 := by
      assumption
    simp [unitTorusFourierIntegrand, hzero']
  have hz := hscaled
  rcases gffUnitBoxComplexFunction_support_subset_centeredBox L R hL hRL f hf hz with
    ⟨hre, him⟩
  change ∀ i : Fin 2, x i ∈ Set.Ioc _ _
  intro i
  fin_cases i
  · change x 0 ∈ Set.Ioc _ _
    constructor
    · simp_all
    · have hupper : x 0 ≤ 1 / 2 := by
        simp_all
      linarith
  · change x 1 ∈ Set.Ioc _ _
    constructor
    · simp_all
    · have hupper : x 1 ≤ 1 / 2 := by
        simp_all
      linarith

/-- A torus Fourier coefficient of a test supported inside the fundamental box is the ordinary
Fourier transform of its scaled compactly supported extension. -/
theorem torusPeriodizationCoeff_eq_fourier
    :
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
      𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) := by
  let E := Complex.measurableEquivPi
  let H := unitTorusFourierIntegrand L f k
  have hHsupport :=
    support_unitTorusFourierIntegrand_subset_box L R hL hRL f hf k
  have hbox := torusPeriodizationCoeff_eq_boxIntegral L f k
  calc
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
        ∫ x in centeredUnitBox,
          UnitAddTorus.mFourier (-k) (fun i => (x i)) •
            torusPeriodizationFunction L f (fun i => (x i)) := by
      assumption
    _ = ∫ x in centeredUnitBox, H x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_centeredUnitBox] with x hx
      rw [unitTorus_mFourier_neg_eq_exp_dot]
      congr 1
      have hx' : x ∈ {x : Fin 2 → ℝ |
          ∀ i, x i ∈ Set.Ioc (-1 / 2) ((-1 / 2) + 1)} := by
        assumption
      have hrep' : torusPeriodizationFunction L f
          (fun i => (x i)) =
          ((f (Complex.equivRealProdCLM.symm (L * x 0, L * x 1)))) := by
        simpa using (torusPeriodizationFunction_rep L f ⟨x, hx'⟩)
      have hpoint : Complex.equivRealProdCLM.symm (L * x 0, L * x 1) =
          L • Complex.measurableEquivPi.symm x := by
        rw [Complex.equivRealProdCLM_symm_apply, Complex.measurableEquivPi_symm_apply]
        apply Complex.ext <;> simp
      rw [hrep', hpoint]
      rfl
    _ = ∫ x, H x := by
      symm
      exact integral_eq_setIntegral_of_support_subset_box
        measurableSet_centeredUnitBox hHsupport
    _ = 𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) := by
      symm
      calc
        𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) =
            ∫ z, Complex.exp
              (↑(-2 * Real.pi * ((innerSL ℝ) z (unitTorusFourierFrequency k))) *
                Complex.I) * gffUnitBoxComplexFunction L f z := by
          rw [Real.fourier_eq']
          apply integral_congr_ae
          filter_upwards [] with z
          congr 1
        _ = ∫ z, H (E z) := by
          apply integral_congr_ae
          filter_upwards [] with z
          simpa [H, E] using
            unitTorusFourierIntegrand_measurableEquivPi L f k z
        _ = ∫ x, H x := (Complex.volume_preserving_equiv_pi).integral_comp' H

end
section
variable (hL : 0 < L)
include hL

/-- Differentiating a test in a physical coordinate multiplies its unit-torus Fourier
coefficient by the corresponding frequency. -/
theorem torusPeriodizationCoeff_unitBoxDirectionalDerivative
    (hRbox : R + 1 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (v : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodizationLp L (unitBoxDirectionalDerivativeTest L f v)) k =
      (2 * Real.pi * Complex.I *
        ((innerSL ℝ) (unitTorusFourierFrequency k) v : ℂ)) *
        UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  have hf' : Function.support f ⊆ ball (0 : ℂ) (R + 1) :=
    hf.trans (ball_subset_ball (by linarith))
  have hfun : gffUnitBoxComplexFunction L (unitBoxDirectionalDerivativeTest L f v) =
      complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v := by
    funext z
    exact gffUnitBoxComplexFunction_unitBoxDirectionalDerivativeTest L
      (ne_of_gt hL) f v z
  rw [torusPeriodizationCoeff_eq_fourier L (R + 1) hL hRbox
    (unitBoxDirectionalDerivativeTest L f v) (support_unitBoxDirectionalDerivativeTest_subset L R f v hf) k]
  rw [hfun]
  rw [fourier_complexDirectionalDerivative
    (gffUnitBoxComplexFunction_contDiff L f)
    (gffUnitBoxComplexFunction_hasCompactSupport L (ne_of_gt hL) f)
    v (unitTorusFourierFrequency k)]
  rw [← torusPeriodizationCoeff_eq_fourier L _ hL hRbox f hf' k]

/-- Two unit-box derivatives multiply the torus coefficient by the squared frequency. -/
theorem torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
    (hRbox : R + 2 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (v : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodizationLp L
          (unitBoxDirectionalDerivativeTest L
            (unitBoxDirectionalDerivativeTest L f v) v)) k =
      (2 * Real.pi * Complex.I *
        ((innerSL ℝ) (unitTorusFourierFrequency k) v : ℂ)) ^ 2 *
        UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  have hone := torusPeriodizationCoeff_unitBoxDirectionalDerivative
    L _ hL (by linarith) _
    (support_unitBoxDirectionalDerivativeTest_subset L R f v hf) v k
  have hzero := torusPeriodizationCoeff_unitBoxDirectionalDerivative
    L R hL (by linarith) f hf v k
  grind

end

end

end DOZZ

end
