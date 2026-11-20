module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightedGram
public import TaoTrudgianYang2025.FourierDecayCore
public import MathCollab.Density.Stronger.Atkinson.SeparatedReciprocal
public import Mathlib
public import LaterPairs.Native.LogCurveDecoupling
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ContinuousPhaseAbel
public import LaterPairs.Native.ContinuousSecondDerivativeRange
public import LaterPairs.Native.ExponentPairShiftJets
public import LaterPairs.Native.FiniteSmoothThirdDerivative
public import LaterPairs.Native.IntegerIntervalCount
public import LaterPairs.Native.RobertSargosCubicJets
public import LaterPairs.Native.RobertSargosDisplacementSums
public import LaterPairs.Native.RobertSargosExponentPair
public import LaterPairs.Native.SargosDoubleLargeSieve
public import LaterPairs.Native.SargosLocalAffineJets
public import LaterPairs.Native.SargosPlanarIntegral
public import LaterPairs.Native.SargosPlanarRegularity
public import LaterPairs.Native.SargosPrefixFourthMajorant
public import LaterPairs.Native.SargosQuarticKernelJets

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxErrors 1000
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025






end TaoTrudgianYang2025
noncomputable section
open MeasureTheory FourierTransform SchwartzMap Set GafniTao
open scoped ComplexConjugate Convolution ContDiff
namespace TaoTrudgianYang2025
private def cutoffConjReflect (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv g)

private theorem cutoffConjReflect_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutoffConjReflect g x = conj (g (-x)) := rfl

private theorem fourier_cutoffConjReflect (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (cutoffConjReflect g) x = conj (𝓕 g x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  rw [← integral_neg_eq_self (fun y : ℝ =>
    Complex.exp (↑(-2 * Real.pi * y * x) * Complex.I) •
      cutoffConjReflect g y) volume]
  apply integral_congr_ae
  filter_upwards with y
  simp only [cutoffConjReflect_apply, neg_neg, smul_eq_mul, map_mul,
    ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

private theorem fourier_fourier_cutoff (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (𝓕 g) x = g (-x) := by
  have h := congrFun (g.continuous.fourierInv_fourier_eq
    g.integrable (𝓕 g).integrable) (-x)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h

private def cutoffSquare (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (𝓕 g) (𝓕 (cutoffConjReflect g))

private theorem cutoffSquare_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutoffSquare g x = (‖𝓕 g x‖^2 : ℝ) := by
  simp only [cutoffSquare, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', fourier_cutoffConjReflect,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem fourier_cutoffSquare (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (cutoffSquare g) x =
      (g ⋆[ContinuousLinearMap.mul ℂ ℂ] cutoffConjReflect g) (-x) := by
  have h : cutoffSquare g =
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        g (cutoffConjReflect g)) :=
    (SchwartzMap.fourier_convolution _ _ _).symm
  rw [h, fourier_fourier_cutoff, SchwartzMap.convolution_apply]

private theorem fourier_cutoffSquare_eq_zero
    (g : 𝓢(ℝ, ℂ)) {R x : ℝ}
    (hs : ∀ y, R < |y| → g y = 0) (hx : 2*R < |x|) :
    𝓕 (cutoffSquare g) x = 0 := by
  rw [fourier_cutoffSquare]
  apply Function.notMem_support.mp
  intro h
  obtain ⟨u,hu,v,hv,huv⟩ :=
    support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) h
  have hu' : |u| ≤ R := le_of_not_gt (fun hn => hu (hs u hn))
  have hv' : |v| ≤ R := by
    apply le_of_not_gt
    intro hn
    apply hv
    rw [cutoffConjReflect_apply, hs (-v) (by simpa only [abs_neg] using hn), map_zero]
  have hsum := abs_add_le u v
  change u+v = -x at huv
  rw [huv, abs_neg] at hsum
  linarith

private def parabolaFrequencyBumpReal : ℝ → ℝ :=
  modelPhaseBufferedCutoff (-1) 1 (1/4)

private theorem parabolaFrequencyBumpReal_smooth :
    ContDiff ℝ ∞ parabolaFrequencyBumpReal :=
  modelPhaseBufferedCutoff_contDiff _ _ _

private theorem parabolaFrequencyBumpReal_compact :
    HasCompactSupport parabolaFrequencyBumpReal :=
  modelPhaseBufferedCutoff_hasCompactSupport (by norm_num)

private def parabolaFrequencyBump : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (parabolaFrequencyBumpReal_compact.toSchwartzMap
      parabolaFrequencyBumpReal_smooth)

private theorem parabolaFrequencyBump_apply (x : ℝ) :
    parabolaFrequencyBump x = (parabolaFrequencyBumpReal x : ℂ) := rfl

private theorem parabolaFrequencyBump_zero {x : ℝ} (hx : 1 < |x|) :
    parabolaFrequencyBump x = 0 := by
  rw [parabolaFrequencyBump_apply]
  apply Complex.ofReal_eq_zero.mpr
  rcases lt_abs.mp hx with h | h
  · exact modelPhaseBufferedCutoff_zero_right (by norm_num) (by linarith)
  · exact modelPhaseBufferedCutoff_zero_left (by norm_num) (by linarith)

private theorem parabolaFrequencyBump_fourier_zero_pos :
    0 < (𝓕 parabolaFrequencyBump 0).re := by
  have hi : Integrable parabolaFrequencyBumpReal :=
    parabolaFrequencyBumpReal_smooth.continuous.integrable_of_hasCompactSupport
      parabolaFrequencyBumpReal_compact
  have hz : parabolaFrequencyBumpReal 0 = 1 :=
    modelPhaseBufferedCutoff_one (by norm_num) (by norm_num) (by norm_num)
  have hp := integral_pos_of_integrable_nonneg_nonzero
    parabolaFrequencyBumpReal_smooth.continuous hi
    (fun x => modelPhaseBufferedCutoff_nonneg _ _ _ x)
    (show parabolaFrequencyBumpReal 0 ≠ 0 by rw [hz]; norm_num)
  have he : (𝓕 parabolaFrequencyBump 0).re = ∫ x, parabolaFrequencyBumpReal x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, parabolaFrequencyBump_apply]
    exact (integral_re (show Integrable (fun x => (parabolaFrequencyBumpReal x : ℂ))
      from parabolaFrequencyBump.integrable)).symm
  rwa [he]

private def cutoffRescale (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) :
    𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 a ha)) f

private theorem cutoffRescale_apply
    (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    cutoffRescale f a ha x = f (a*x) := rfl

private theorem fourier_cutoffRescale
    (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (cutoffRescale f a ha) ξ = |a⁻¹| • 𝓕 f (ξ/a) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ x : ℝ, (fun y : ℝ =>
      Complex.exp (↑(-2*Real.pi*y*(ξ/a))*Complex.I) • f y) (a*x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [cutoffRescale_apply]
      congr 3
      field_simp
    _ = _ := by
      simpa using Measure.integral_comp_mul_left
        (fun y : ℝ => Complex.exp (↑(-2*Real.pi*y*(ξ/a))*Complex.I) • f y) a

private theorem cutoff_polynomial_decay (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1+|x|)^n*‖f x‖ ≤ C := by
  let B : ℝ := 2^n * (Finset.Iic (n,0)).sup
    (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (n,0)) (k := n) (n := 0) le_rfl le_rfl f x
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

theorem exists_parabola_rapid_cutoff :
    ∃ η : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, 0 ≤ (η x).re ∧ (η x).im = 0) ∧
      (∀ x : ℝ, |x| ≤ 1 → 1 ≤ (η x).re) ∧
      (∀ ξ : ℝ, 1/100 ≤ |ξ| → 𝓕 η ξ = 0) ∧
      (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, (1+|x|)^n*‖η x‖ ≤ C) := by
  let f := cutoffSquare parabolaFrequencyBump
  have hf (x : ℝ) : f x = (‖𝓕 parabolaFrequencyBump x‖^2 : ℝ) :=
    cutoffSquare_apply _ _
  have hfn (x : ℝ) : 0 ≤ (f x).re := by rw [hf]; exact sq_nonneg _
  have hfi (x : ℝ) : (f x).im = 0 := by rw [hf]; rfl
  have hf₀ : 0 < (f 0).re := by
    rw [hf,Complex.ofReal_re]
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    have h := parabolaFrequencyBump_fourier_zero_pos
    rw [hz] at h
    simp at h
  let m : ℝ := (f 0).re/2
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : {x : ℝ | m < (f x).re} ∈ nhds 0 :=
    ((Complex.continuous_re.comp f.continuous).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds (by dsimp [m]; linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  let a : ℝ := min (δ/2) (1/400)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  let η : 𝓢(ℝ, ℂ) := (m⁻¹ : ℂ) • cutoffRescale f a ha.ne'
  have he (x : ℝ) : η x = (m⁻¹ : ℂ)*f (a*x) := rfl
  have her (x : ℝ) : (η x).re = m⁻¹*(f (a*x)).re := by
    rw [he,Complex.mul_re]
    simp
  have hei (x : ℝ) : (η x).im = 0 := by
    rw [he,Complex.mul_im,hfi]
    simp
  refine ⟨η,fun x => ⟨?_,hei x⟩,?_,?_,cutoff_polynomial_decay η⟩
  · rw [her]
    exact mul_nonneg (inv_nonneg.mpr hm.le) (hfn _)
  · intro x hx
    have hxδ : a*|x| < δ := by
      have hax := mul_le_mul_of_nonneg_left hx ha.le
      have haδ : a ≤ δ/2 := min_le_left _ _
      nlinarith
    have hmx := hball (show a*x ∈ Metric.ball 0 δ by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_mul,abs_of_pos ha]
        using hxδ)
    rw [her]
    apply (le_inv_mul_iff₀ hm).mpr
    simpa only [mul_one] using le_of_lt hmx
  · intro ξ hξ
    change 𝓕 ((m⁻¹ : ℂ) • cutoffRescale f a ha.ne') ξ = 0
    rw [fourier_smul]
    change (m⁻¹ : ℂ) • 𝓕 (cutoffRescale f a ha.ne') ξ = 0
    rw [fourier_cutoffRescale,
      fourier_cutoffSquare_eq_zero parabolaFrequencyBump
        (fun y hy => parabolaFrequencyBump_zero hy)]
    · simp
    · rw [abs_div,abs_of_pos ha]
      apply (lt_div_iff₀ ha).mpr
      have hab : a ≤ 1/400 := min_le_right _ _
      linarith

def parabolaRapidProfile : 𝓢(ℝ, ℂ) :=
  Classical.choose exists_parabola_rapid_cutoff

private theorem parabolaRapidProfile_nonneg (x : ℝ) :
    0 ≤ (parabolaRapidProfile x).re :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).1 x |>.1

private theorem parabolaRapidProfile_real (x : ℝ) :
    (parabolaRapidProfile x).im = 0 :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).1 x |>.2

private theorem parabolaRapidProfile_one_le (x : ℝ) (hx : |x| ≤ 1) :
    1 ≤ (parabolaRapidProfile x).re :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).2.1 x hx

private theorem parabolaRapidProfile_fourier_zero (ξ : ℝ) (hξ : 1/100 ≤ |ξ|) :
    𝓕 parabolaRapidProfile ξ = 0 :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).2.2.1 ξ hξ

private theorem parabolaRapidProfile_coe_re (x : ℝ) :
    ((parabolaRapidProfile x).re : ℂ) = parabolaRapidProfile x := by
  apply Complex.ext
  · rfl
  · simpa using (parabolaRapidProfile_real x).symm

def parabolaRapidKernel (R c x : ℝ) : ℝ :=
  (parabolaRapidProfile ((x-c)/R)).re

theorem parabolaRapidKernel_nonneg (R c x : ℝ) :
    0 ≤ parabolaRapidKernel R c x := parabolaRapidProfile_nonneg _

theorem parabolaRapidKernel_one_le {R c x : ℝ}
    (hR : 0 < R) (hx : |x-c| ≤ R) :
    1 ≤ parabolaRapidKernel R c x := by
  apply parabolaRapidProfile_one_le
  rw [abs_div,abs_of_pos hR]
  exact (div_le_one hR).mpr hx

theorem integrable_parabolaRapidKernel {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable (parabolaRapidKernel R c) := by
  have h₀ : Integrable (cutoffRescale parabolaRapidProfile R⁻¹
    (inv_ne_zero hR.ne')) := (cutoffRescale parabolaRapidProfile R⁻¹
      (inv_ne_zero hR.ne')).integrable
  have h := h₀.re.comp_add_right (-c)
  convert h using 1
  ext x
  simp only [parabolaRapidKernel,cutoffRescale_apply,sub_eq_add_neg,div_eq_mul_inv,mul_comm]
  rfl

theorem parabolaRapidKernel_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R c x : ℝ,
      (1+|(x-c)/R|)^n*parabolaRapidKernel R c x ≤ C := by
  obtain ⟨C,hC,h⟩ := cutoff_polynomial_decay parabolaRapidProfile n
  refine ⟨C,hC,fun R c x => ?_⟩
  have he : ‖parabolaRapidProfile ((x-c)/R)‖ = parabolaRapidKernel R c x := by
    rw [← parabolaRapidProfile_coe_re,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (parabolaRapidProfile_nonneg _)]
    rfl
  simpa only [he] using h ((x-c)/R)

private theorem integral_parabolaRapidKernel_character_zero_origin
    {R ξ : ℝ} (hR : 0 < R) (hξ : 1/(100*R) ≤ |ξ|) :
    (∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) = 0 := by
  have he : (∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) =
      𝓕 (cutoffRescale parabolaRapidProfile R⁻¹ (inv_ne_zero hR.ne')) (-ξ) := by
    rw [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [parabolaRapidKernel,sub_zero,parabolaRapidProfile_coe_re,
      cutoffRescale_apply,fordAdditiveCharacter,smul_eq_mul]
    rw [show R⁻¹*x = x/R by ring]
    rw [mul_comm (parabolaRapidProfile (x/R))]
    congr 2
    push_cast
    ring
  rw [he,fourier_cutoffRescale,parabolaRapidProfile_fourier_zero]
  · simp
  · rw [div_inv_eq_mul,abs_mul,abs_neg,abs_of_pos hR]
    have h := (div_le_iff₀ (by positivity : 0 < 100*R)).mp hξ
    nlinarith

theorem integral_parabolaRapidKernel_character_zero
    {R ξ : ℝ} (hR : 0 < R) (hξ : 1/(100*R) ≤ |ξ|) (c : ℝ) :
    (∫ x : ℝ, (parabolaRapidKernel R c x : ℂ)*fordAdditiveCharacter (ξ*x)) = 0 := by
  let f : ℝ → ℂ := fun x =>
    (parabolaRapidKernel R c x : ℂ)*fordAdditiveCharacter (ξ*x)
  have ht := integral_add_right_eq_self (μ := volume) f c
  calc
    _ = ∫ x : ℝ, f (x+c) := ht.symm
    _ = ∫ x : ℝ, fordAdditiveCharacter (ξ*c)*
      ((parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [f,parabolaRapidKernel]
      rw [add_sub_cancel_right,sub_zero,
        show ξ*(x+c) = ξ*c+ξ*x by ring,fordAdditiveCharacter_add]
      ring
    _ = fordAdditiveCharacter (ξ*c)*
      ∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x) :=
        integral_const_mul _ _
    _ = 0 := by rw [integral_parabolaRapidKernel_character_zero_origin hR hξ,mul_zero]

def parabolaRapidWeight (R r t α γ : ℝ) : ℝ :=
  parabolaRapidKernel R r α * parabolaRapidKernel R t γ

theorem parabolaRapidWeight_nonneg (R r t α γ : ℝ) :
    0 ≤ parabolaRapidWeight R r t α γ :=
  mul_nonneg (parabolaRapidKernel_nonneg _ _ _) (parabolaRapidKernel_nonneg _ _ _)

theorem parabolaRapidWeight_one_le {R r t α γ : ℝ}
    (hR : 0 < R) (hα : |α-r| ≤ R) (hγ : |γ-t| ≤ R) :
    1 ≤ parabolaRapidWeight R r t α γ := by
  exact one_le_mul_of_one_le_of_one_le
    (parabolaRapidKernel_one_le hR hα) (parabolaRapidKernel_one_le hR hγ)

theorem parabolaRapidWeight_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r t α γ : ℝ,
      (1+|(α-r)/R|+|(γ-t)/R|)^n*parabolaRapidWeight R r t α γ ≤ C := by
  obtain ⟨C,hC,h⟩ := parabolaRapidKernel_decay n
  refine ⟨C^2,sq_pos_of_pos hC,fun R r t α γ => ?_⟩
  have hp : 1+|(α-r)/R|+|(γ-t)/R| ≤
      (1+|(α-r)/R|)*(1+|(γ-t)/R|) := by
    nlinarith [mul_nonneg (abs_nonneg ((α-r)/R)) (abs_nonneg ((γ-t)/R))]
  have hpn := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|(α-r)/R|+|(γ-t)/R|) hp n
  have hprod := mul_le_mul (h R r α) (h R t γ)
    (mul_nonneg (by positivity) (parabolaRapidKernel_nonneg _ _ _)) hC.le
  have hm := mul_le_mul_of_nonneg_right hpn (parabolaRapidWeight_nonneg R r t α γ)
  rw [mul_pow] at hm
  unfold parabolaRapidWeight at hm ⊢
  nlinarith only [hm,hprod]

theorem integral_parabolaRapidWeight_character_zero
    {R u v : ℝ} (hR : 0 < R)
    (hgap : 1/(100*R) ≤ |u| ∨ 1/(100*R) ≤ |v|) (r t : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, (parabolaRapidWeight R r t α γ : ℂ)*
      fordAdditiveCharacter (u*α+v*γ)) = 0 := by
  have he (α γ : ℝ) :
      (parabolaRapidWeight R r t α γ : ℂ)*fordAdditiveCharacter (u*α+v*γ) =
      ((parabolaRapidKernel R r α : ℂ)*fordAdditiveCharacter (u*α))*
      ((parabolaRapidKernel R t γ : ℂ)*fordAdditiveCharacter (v*γ)) := by
    rw [fordAdditiveCharacter_add]
    unfold parabolaRapidWeight
    push_cast
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const]
  rcases hgap with h | h
  · rw [integral_parabolaRapidKernel_character_zero hR h,zero_mul]
  · rw [integral_parabolaRapidKernel_character_zero hR h,mul_zero]

private theorem continuous_rapidWeight (R r t : ℝ) :
    Continuous (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) := by
  unfold parabolaRapidWeight parabolaRapidKernel
  exact (Complex.continuous_re.comp
    (parabolaRapidProfile.continuous.comp (by fun_prop))).mul
    (Complex.continuous_re.comp
      (parabolaRapidProfile.continuous.comp (by fun_prop)))

private theorem rapid_weighted_integrable {f : ℝ × ℝ → ℂ}
    (hf : Continuous f) {M R : ℝ} (hR : 0 < R)
    (hM : ∀ p, ‖f p‖ ≤ M) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (parabolaRapidWeight R r t p.1 p.2 : ℂ)*f p) := by
  have hw : Integrable (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have hc := (Complex.continuous_ofReal.comp (continuous_rapidWeight R r t)).mul hf
  apply (hw.mul_const M).mono' hc.aestronglyMeasurable
  filter_upwards with p
  change ‖(parabolaRapidWeight R r t p.1 p.2 : ℂ)*f p‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (parabolaRapidWeight_nonneg R r t p.1 p.2)]
  exact mul_le_mul_of_nonneg_left (hM p) (parabolaRapidWeight_nonneg R r t p.1 p.2)

private theorem rapidCharacter_integrable {R : ℝ} (hR : 0 < R) (r t u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2)) :=
  rapid_weighted_integrable (by unfold fordAdditiveCharacter; fun_prop) hR
    (fun p => (sargos_character_norm _).le) r t

def parabolaRapidBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, parabolaRapidWeight R r t p.1 p.2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

def parabolaSourceWeight (R r t α γ : ℝ) : ℝ :=
  1/(1+‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖)^100

theorem parabolaSourceWeight_nonneg (R r t α γ : ℝ) :
    0 ≤ parabolaSourceWeight R r t α γ := by
  unfold parabolaSourceWeight
  positivity

private theorem continuous_sourceWeight (R r t : ℝ) :
    Continuous (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) := by
  unfold parabolaSourceWeight
  exact continuous_const.div (by fun_prop) (fun p => by positivity)

theorem integrable_parabolaSourceWeight {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) := by
  have hb := integrable_one_add_norm (E := ℝ × ℝ) (μ := volume) (r := 100)
    (by norm_num)
  have hi := (hb.comp_smul (inv_ne_zero hR.ne')).comp_add_right (-(r,t))
  apply hi.mono' (continuous_sourceWeight R r t).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)]
  have hnorm : ‖R⁻¹ • (p + -(r,t))‖ ≤
      ‖(((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I‖ := by
    rw [Prod.norm_def]
    apply max_le
    · have h := Complex.abs_re_le_norm
        ((((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I)
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at h
      change |R⁻¹*(p.1 + -r)| ≤ _
      simpa only [sub_eq_add_neg,div_eq_mul_inv,mul_comm] using h
    · have h := Complex.abs_im_le_norm
        ((((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I)
      simp only [Complex.add_im,Complex.ofReal_re,Complex.mul_im,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero] at h
      change |R⁻¹*(p.2 + -t)| ≤ _
      simpa only [sub_eq_add_neg,div_eq_mul_inv,mul_comm] using h
  rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]
  change 1/(1+‖(((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I‖)^100 ≤ _
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem parabolaRapidWeight_le_sourceWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ R r t α γ : ℝ,
      parabolaRapidWeight R r t α γ ≤ C*parabolaSourceWeight R r t α γ := by
  obtain ⟨C,hC,h⟩ := parabolaRapidWeight_decay 100
  refine ⟨C,hC,fun R r t α γ => ?_⟩
  have hn : ‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖ ≤
      |(α-r)/R|+|(γ-t)/R| := by
    simpa using Complex.norm_le_abs_re_add_abs_im
      ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I)
  have hp : (1+‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖)^100 ≤
      (1+|(α-r)/R|+|(γ-t)/R|)^100 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_right hp (parabolaRapidWeight_nonneg R r t α γ)
  unfold parabolaSourceWeight
  rw [mul_one_div,le_div_iff₀ (by positivity)]
  rw [mul_comm]
  exact hm.trans (h R r t α γ)

private def parabolaMomentFunction {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
  ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabolaMomentFunction_nonneg {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (p : ℝ × ℝ) :
    0 ≤ parabolaMomentFunction S V z c x y p := by
  unfold parabolaMomentFunction
  positivity

private theorem parabolaMomentFunction_continuous {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    Continuous (parabolaMomentFunction S V z c x y) := by
  unfold parabolaMomentFunction sargosPlanarSum fordAdditiveCharacter
  fun_prop

private theorem parabolaMomentFunction_integrable {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W p*parabolaMomentFunction S V z c x y p) := by
  apply hW.mul_bdd (parabolaMomentFunction_continuous S V z c x y).aestronglyMeasurable
    (c := (∑ i ∈ S, ‖z i‖)^2*(∑ j ∈ V, ‖c j‖)^4)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)]
  unfold parabolaMomentFunction
  have hS := norm_sargosPlanarSum_le_sum_norm S z x (fun i => (x i)^2) p.1 p.2
  have hV := norm_sargosPlanarSum_le_sum_norm V c y (fun j => (y j)^2) p.1 p.2
  gcongr

def parabolaSourceBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, parabolaSourceWeight R r t p.1 p.2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

def parabolaBoxBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabolaBox_le_rapid {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    parabolaBoxBilinearMoment S V z c x y R r t ≤
      parabolaRapidBilinearMoment S V z c x y R r t := by
  let F := parabolaMomentFunction S V z c x y
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  have hiF : IntegrableOn F B := ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
    (parabolaMomentFunction_continuous S V z c x y).continuousOn
  have hiW : Integrable W :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have hi := parabolaMomentFunction_integrable S V z c x y hiW
  have hpoint (p : ℝ × ℝ) (hp : p ∈ B) : F p ≤ W p*F p := by
    have hα : |p.1-r| ≤ R := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
    have hγ : |p.2-t| ≤ R := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    have hW := parabolaRapidWeight_one_le hR hα hγ
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hW
      (parabolaMomentFunction_nonneg S V z c x y p)
  have hlocal := setIntegral_mono_on hiF hi.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  have hwhole := setIntegral_le_integral (s := B) hi
    (Filter.Eventually.of_forall (fun p =>
      mul_nonneg (parabolaRapidWeight_nonneg _ _ _ _ _)
        (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)))
  simpa only [parabolaBoxBilinearMoment,parabolaRapidBilinearMoment,F,W,B,
    parabolaMomentFunction,mul_assoc] using hlocal.trans hwhole

private theorem parabolaRapid_le_source {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {C R : ℝ} (hR : 0 < R)
    (hC : ∀ R r t α γ : ℝ,
      parabolaRapidWeight R r t α γ ≤ C*parabolaSourceWeight R r t α γ)
    (r t : ℝ) :
    parabolaRapidBilinearMoment S V z c x y R r t ≤
      C*parabolaSourceBilinearMoment S V z c x y R r t := by
  have hiR := parabolaMomentFunction_integrable S V z c x y
    ((integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t))
  have hiS := parabolaMomentFunction_integrable S V z c x y
    (integrable_parabolaSourceWeight hR r t)
  have hb := integral_mono hiR (hiS.const_mul C)
    (fun p => by
      have h := mul_le_mul_of_nonneg_right (hC R r t p.1 p.2)
        (parabolaMomentFunction_nonneg S V z c x y p)
      simpa only [parabolaRapidWeight,mul_assoc] using h)
  rw [integral_const_mul] at hb
  simpa only [parabolaRapidBilinearMoment,parabolaSourceBilinearMoment,
    parabolaMomentFunction,parabolaRapidWeight,mul_assoc] using hb

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

end TaoTrudgianYang2025
noncomputable section
namespace TaoTrudgianYang2025
open MeasureTheory Set
open scoped BigOperators
private theorem sourceWeight_triangle (R r t α γ β δ : ℝ) :
    ‖(((β-r)/R : ℝ) : ℂ)+((δ-t)/R : ℝ)*Complex.I‖ ≤
      ‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖+
      ‖(((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I‖ := by
  have heq :
      (((β-r)/R : ℝ) : ℂ)+((δ-t)/R : ℝ)*Complex.I =
        ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I)+
        ((((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I) := by
    push_cast
    ring
  rw [heq]
  exact norm_add_le _ _

private theorem parabolaSourceWeight_triangle_lower (R r t α γ β δ : ℝ) :
    parabolaSourceWeight R r t α γ * parabolaSourceWeight R α γ β δ ≤
      parabolaSourceWeight R r t β δ := by
  have h := sourceWeight_triangle R r t α γ β δ
  have hm := mul_nonneg
    (norm_nonneg ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I))
    (norm_nonneg ((((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I))
  unfold parabolaSourceWeight
  rw [div_mul_div_comm,one_mul,← mul_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by nlinarith only [h,hm]) _

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators NNReal ENNReal
namespace TaoTrudgianYang2025
open LogarithmicSixth
open scoped ENNReal
universe u

def ParabolaWeightBand (δ : ℝ) (W : ℝ × ℝ → ℝ) : Prop :=
  (∀ p, 0 ≤ W p) ∧ Integrable W ∧
    ∀ ξ κ : ℝ, δ^2 ≤ parabolaBandGauge ξ κ →
      (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter (ξ*p.1+κ*p.2)) = 0

theorem parabolaRapidWeight_band {δ R : ℝ} (hR : 0 < R)
    (hwidth : 3/(100*R) ≤ δ^2) (r t : ℝ) :
    ParabolaWeightBand δ (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) := by
  refine ⟨fun p => parabolaRapidWeight_nonneg _ _ _ _ _,
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t),?_⟩
  intro ξ κ hgap
  have hgap' : 1/(100*R) ≤ |ξ| ∨ 1/(100*R) ≤ |κ| := by
    by_contra h
    push Not at h
    have hh : 3*(1/(100*R)) ≤ δ^2 := by
      simpa only [div_eq_mul_inv,one_mul] using hwidth
    have ht : |κ-2*ξ| ≤ |κ|+2*|ξ| := by
      simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using abs_sub κ (2*ξ)
    have hm : parabolaBandGauge ξ κ < δ^2 :=
      max_lt (by linarith [h.2,show 0 < 1/(100*R) by positivity])
        (by linarith [h.1,h.2])
    exact (not_lt_of_ge hgap) hm
  have hi := rapidCharacter_integrable hR r t ξ κ
  have he := integral_prod
    (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter (ξ*p.1+κ*p.2)) hi
  exact he.trans (integral_parabolaRapidWeight_character_zero hR hgap' r t)

def parabolaWeightedBilinearMoment {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (S : Finset ι) (V : Finset τ)
    (z : ι → ℂ) (c : τ → ℂ) (x : ι → ℝ) (y : τ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, W p*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem weighted_integral_cauchy_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {W P Q : α → ℝ}
    (hW : ∀ x, 0 ≤ W x)
    (hPP : Integrable (fun x => W x*(P x)^2) μ)
    (hPQ : Integrable (fun x => W x*P x*Q x) μ)
    (hQQ : Integrable (fun x => W x*(Q x)^2) μ) :
    (∫ x, W x*P x*Q x ∂μ)^2 ≤
      (∫ x, W x*(P x)^2 ∂μ)*(∫ x, W x*(Q x)^2 ∂μ) := by
  have hquad (a : ℝ) :
      0 ≤ (∫ x, W x*(P x)^2 ∂μ)*(a*a) +
        (-2*(∫ x, W x*P x*Q x ∂μ))*a +
        (∫ x, W x*(Q x)^2 ∂μ) := by
    have heq (x : α) : W x*(a*P x-Q x)^2 =
        a^2*(W x*(P x)^2) - (2*a)*(W x*P x*Q x) + W x*(Q x)^2 := by ring
    have hp : 0 ≤ ∫ x, W x*(a*P x-Q x)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hW x) (sq_nonneg _))
    simp_rw [heq] at hp
    have hA : Integrable (fun x => a^2*(W x*(P x)^2)) μ := hPP.const_mul _
    have hB : Integrable (fun x => (2*a)*(W x*P x*Q x)) μ := hPQ.const_mul _
    have hAB : Integrable (fun x => a^2*(W x*(P x)^2)-(2*a)*(W x*P x*Q x)) μ := hA.sub hB
    rw [integral_add hAB hQQ,
      integral_sub hA hB,
      integral_const_mul,integral_const_mul] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

def parabolaWeightedSixNorm {ι : Type*} (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) : ℝ :=
  lpNorm (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2)
    6 (volume.withDensity (fun p => ENNReal.ofReal (W p)))

theorem parabolaWeightedSixNorm_nonneg {ι : Type*} (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    0 ≤ parabolaWeightedSixNorm W S z x := lpNorm_nonneg

theorem parabolaWeightedSixNorm_pow_six {ι : Type*} (W : ℝ × ℝ → ℝ)
    (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (parabolaWeightedSixNorm W S z x)^6 =
      parabolaWeightedBilinearMoment W S S z z x x := by
  simpa only [parabolaWeightedSixNorm, parabolaWeightedBilinearMoment,
    logCurveWeightedSixNorm, logCurveWeightedBilinearMoment, logCurve_zero] using
    logCurveWeightedSixNorm_pow_six 0 W hW₀ hW S z x

def ParabolaDecouplingBound (n : ℕ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (ι : Type u) (W : ℝ × ℝ → ℝ), ParabolaWeightBand (1/(n:ℝ)) W →
    ∀ (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ),
      (∀ j, ∀ k ∈ S j, x j k ∈ Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ))) →
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
        D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2

theorem exists_parabolaDecouplingBound_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ,
      ParabolaDecouplingBound.{u} (2^n) (C*(2:ℝ)^(ε*n)) := by
  obtain ⟨C, hC, h⟩ := exists_logCurveDecouplingBound_dyadic.{u} hε
  refine ⟨C, hC, fun n => ⟨(h n).1, ?_⟩⟩
  intro ι W hW S z x hx
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) (1/4) := by norm_num
  have hband : LogCurveWeightBand 0 (1 / ((2^n : ℕ) : ℝ)) W := by
    simpa only [ParabolaWeightBand, LogCurveWeightBand, logCurveBandGauge, add_zero, one_pow,
      div_one, one_mul] using hW
  simpa only [parabolaWeightedSixNorm, logCurveWeightedSixNorm, logCurve_zero] using
    (h n).2 0 hzero ι W hband S z x hx

theorem exists_parabolaBox_dyadic_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := exists_parabolaDecouplingBound_dyadic.{u}
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : ParabolaWeightBand (1/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaRapidWeight_band hR hwidth r t
  have hnorm := (hD n).2 ι W hW S z x hx
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hbox := parabolaBox_le_rapid (Finset.univ.sigma S) (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t
  have hid := parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have he : parabolaRapidBilinearMoment
      (Finset.univ.sigma S) (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t =
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^6 := by
    simpa only [parabolaRapidBilinearMoment,parabolaWeightedBilinearMoment,W] using hid.symm
  exact hbox.trans (he.le.trans hcube)
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem parabola_sixNorm_weight_comparison {ι : Type*}
    {V W : ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hV₀ : ∀ p, 0 ≤ V p) (hW₀ : ∀ p, 0 ≤ W p)
    (hV : Integrable V) (hW : Integrable W) (hVW : ∀ p, V p ≤ C*W p)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (parabolaWeightedSixNorm V S z x)^2 ≤
      C^((3:ℝ)⁻¹)*(parabolaWeightedSixNorm W S z x)^2 := by
  have hm : parabolaWeightedBilinearMoment V S S z z x x ≤
      C*parabolaWeightedBilinearMoment W S S z z x x := by
    have h := integral_mono
      (parabolaMomentFunction_integrable S S z z x x hV)
      ((parabolaMomentFunction_integrable S S z z x x hW).const_mul C)
      (fun p => (mul_le_mul_of_nonneg_right (hVW p)
        (parabolaMomentFunction_nonneg S S z z x x p)).trans_eq (by ring))
    rw [integral_const_mul] at h
    simpa only [parabolaWeightedBilinearMoment,parabolaMomentFunction,mul_assoc] using h
  apply (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  rw [mul_pow,←pow_mul,←pow_mul]
  have hroot := Real.rpow_inv_natCast_pow hC (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot]
  norm_num only [show (2*3:ℕ)=6 by omega]
  rw [parabolaWeightedSixNorm_pow_six V hV₀ hV,
    parabolaWeightedSixNorm_pow_six W hW₀ hW]
  exact hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

theorem exists_parabolaBox_sourceWeight_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨C,hC,hbox⟩ := exists_parabolaBox_dyadic_decoupling.{u} hε
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨C*K,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx
  have hm := hbox n R r t hR hwidth ι S z x hx
  have hnorm (j : Fin (2^n)) :=
    parabola_sixNorm_weight_comparison hK.le
      (fun p : ℝ × ℝ => parabolaRapidWeight_nonneg R r t p.1 p.2)
      (fun p : ℝ × ℝ => parabolaSourceWeight_nonneg R r t p.1 p.2)
      (parabolaRapidWeight_band hR hwidth r t).2.1
      (integrable_parabolaSourceWeight hR r t)
      (fun p => hcomp R r t p.1 p.2) (S j) (z j) (x j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hs
  have hcube := pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
  rw [mul_pow] at hcube
  have hroot := Real.rpow_inv_natCast_pow hK.le (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot] at hcube
  calc
    _ ≤ _ := hm
    _ ≤ C*(2:ℝ)^(ε*n)*(K*
        (∑ j, (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
          (S j) (z j) (x j))^2)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem parabola_sourceWeight_horizontal_translate {R : ℝ} (hR : 0 < R)
    (r t α γ u : ℝ) :
    parabolaSourceWeight R r t (α-u) γ ≤
      (1+|u|/R)^100*parabolaSourceWeight R r t α γ := by
  have h := parabolaSourceWeight_triangle_lower R r t (α-u) γ α γ
  have he : parabolaSourceWeight R (α-u) γ α γ = 1/(1+|u|/R)^100 := by
    unfold parabolaSourceWeight
    have hx : (α-(α-u))/R=u/R := by ring
    rw [hx,sub_self,zero_div,Complex.ofReal_zero,zero_mul,add_zero,
      Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hR]
  rw [he,mul_one_div] at h
  rw [div_le_iff₀ (by positivity)] at h
  simpa only [mul_comm] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff
namespace TaoTrudgianYang2025

private def bourgainCubicQuarticCutoff (a b s : ℝ) : ℂ :=
  (modelPhaseBufferedCutoff (-2) 2 (1/2) s : ℂ)*
    fordAdditiveCharacter (a*s^3+b*s^4)

private def bourgainCubicQuarticJoint (p : (ℝ × ℝ) × ℝ) : ℂ :=
  bourgainCubicQuarticCutoff p.1.1 p.1.2 p.2

private theorem bourgainCubicQuarticJoint_smooth :
    ContDiff ℝ ∞ bourgainCubicQuarticJoint := by
  have hc : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
      (modelPhaseBufferedCutoff (-2) 2 (1/2) p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((modelPhaseBufferedCutoff_contDiff (-2) 2 (1/2)).comp contDiff_snd)
  unfold bourgainCubicQuarticJoint bourgainCubicQuarticCutoff fordAdditiveCharacter
  apply hc.mul
  have hp : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => p.1.1*p.2^3+p.1.2*p.2^4) :=
    ((contDiff_fst.fst).mul (contDiff_snd.pow 3)).add
      ((contDiff_fst.snd).mul (contDiff_snd.pow 4))
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp

private theorem bourgainCubicQuarticCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (bourgainCubicQuarticCutoff a b) := by
  have hmap : ContDiff ℝ ∞ (fun s : ℝ => ((a,b),s)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def,bourgainCubicQuarticJoint] using
    bourgainCubicQuarticJoint_smooth.comp hmap

private theorem bourgainCubicQuarticCutoff_support (a b : ℝ) :
    tsupport (bourgainCubicQuarticCutoff a b) ⊆ Icc (-2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hk : s ∈ tsupport (modelPhaseBufferedCutoff (-2) 2 (1/2)) := by
    apply subset_closure
    intro hz
    exact hs (by rw [bourgainCubicQuarticCutoff,hz,Complex.ofReal_zero,zero_mul])
  have hb := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/2) hk
  constructor <;> linarith [hb.1,hb.2]

private theorem norm_vertical_slice_iteratedFDeriv
    (F : (ℝ × ℝ) × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (s : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun x => F (p,x)) s‖ ≤
      ‖iteratedFDeriv ℝ j F (p,s)‖ := by
  let L : ℝ →L[ℝ] (ℝ × ℝ) × ℝ := ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
  have hL : ‖L‖=1 := ContinuousLinearMap.norm_inr ℝ (ℝ × ℝ) ℝ
  have hshift : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => (p,0)+q) :=
    contDiff_const.add contDiff_id
  have hf : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => F ((p,0)+q)) :=
    hF.comp hshift
  have he : (fun x => F (p,x)) = (fun q => F ((p,0)+q)) ∘ L := by
    ext x; simp [L]
  rw [he,L.iteratedFDeriv_comp_right hf s (i:=j)
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)),iteratedFDeriv_comp_add_left]
  have hp : (p,0)+L s = (p,s) := by simp [L]
  rw [hp]
  have h := (iteratedFDeriv ℝ j F (p,s)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  simpa only [hL,Finset.prod_const_one,mul_one] using h

private theorem bourgainCubicQuarticCutoff_derivative_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ s : ℝ, ∀ j ≤ Q,
        ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ ≤ C := by
  let F := bourgainCubicQuarticJoint
  let B := fun p : (ℝ × ℝ) × ℝ =>
    ∑ j ∈ Finset.range (Q+1), ‖iteratedFDeriv ℝ j F p‖
  have hB : Continuous B := continuous_finsetSum _ fun j _ =>
    (bourgainCubicQuarticJoint_smooth.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ×ˢ Icc (-2:ℝ) 2) hB.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro a ha b hb s j hj
  by_cases hs : s ∈ Icc (-2:ℝ) 2
  · have hnorm : ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ ≤
        ‖iteratedFDeriv ℝ j F ((a,b),s)‖ := by
      simpa only [F,bourgainCubicQuarticJoint] using
        norm_vertical_slice_iteratedFDeriv F bourgainCubicQuarticJoint_smooth (a,b) s j
    have hsum : ‖iteratedFDeriv ℝ j F ((a,b),s)‖ ≤ B ((a,b),s) := by
      dsimp only [B]
      exact Finset.single_le_sum (fun k _ => norm_nonneg (iteratedFDeriv ℝ k F ((a,b),s)))
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    exact hnorm.trans (hsum.trans ((le_abs_self _).trans
      ((hM _ ⟨⟨ha,hb⟩,hs⟩).trans (le_max_left _ _))))
  · have hz : iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hs (bourgainCubicQuarticCutoff_support a b
        ((tsupport_iteratedFDeriv_subset j) (subset_closure h)))
    rw [hz,norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

/-- Uniform weighted Fourier inversion for a family of compactly supported
cutoffs that agrees with a phase on the unit interval. -/
public theorem exists_cutoff_multiplier_kernel {α : Type*} {P : Set α}
    (f : α → ℝ → ℂ) (phase : α → ℝ → ℝ)
    (hcont : ∀ p ∈ P, Continuous (f p))
    (hsup : ∀ p ∈ P, HasCompactSupport (f p))
    (hdec : ∃ D : ℝ, 0 < D ∧ ∀ p ∈ P, ∀ ξ : ℝ, (1+|ξ|)^102*‖𝓕 (f p) ξ‖ ≤ D)
    (hcut : ∀ p ∈ P, ∀ s ∈ Icc (-1:ℝ) 1, f p s = fordAdditiveCharacter (phase p s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ P, ∃ K : ℝ → ℂ, Continuous K ∧
      Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
      (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C ∧
      (∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) ∧
      ∀ s ∈ Icc (-1:ℝ) 1, fordAdditiveCharacter (phase p s) =
        ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  obtain ⟨D,hD,hdecay⟩ := hdec
  refine ⟨max D (D*Real.pi),hD.trans_le (le_max_left _ _),?_⟩
  intro p hp
  let K : ℝ → ℂ := 𝓕 (f p)
  have hi : Integrable (f p) := (hcont p hp).integrable_of_hasCompactSupport (hsup p hp)
  have hKc : Continuous K :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hdom (ξ : ℝ) : (1+|ξ|)^100*‖K ξ‖≤D*(1+ξ^2)⁻¹ := by
    have hs : 1+ξ^2≤(1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
    have hp : (1+ξ^2)*((1+|ξ|)^100*‖K ξ‖)≤D := by
      calc
        _ ≤ (1+|ξ|)^2*((1+|ξ|)^100*‖K ξ‖) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _ = (1+|ξ|)^102*‖K ξ‖ := by
          rw [show (102:ℕ)=2+100 by omega,pow_add]
          ring
        _ ≤ D := hdecay p hp ξ
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using hp
  have hweightCont : Continuous (fun ξ : ℝ => (1+|ξ|)^100*‖K ξ‖) :=
    ((continuous_const.add continuous_abs).pow 100).mul hKc.norm
  have hKi : Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖K ξ‖) :=
    (integrable_inv_one_add_sq.const_mul D).mono' hweightCont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤
          (1+|ξ|)^100*‖K ξ‖ by positivity)] using hdom ξ))
  have hmass : (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖)≤D*Real.pi := by
    have h := integral_mono hKi (integrable_inv_one_add_sq.const_mul D) hdom
    simpa only [integral_const_mul,integral_univ_inv_one_add_sq] using h
  have hK : Integrable K := hKi.mono' hKc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by linarith [abs_nonneg ξ]) : (1:ℝ)≤(1+|ξ|)^100)
        (norm_nonneg (K ξ))))
  refine ⟨K,hKc,hKi,hmass.trans (le_max_right _ _),?_,?_⟩
  · intro ξ
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (hdecay p hp ξ).trans (le_max_left D (D*Real.pi))
  intro s hs
  have hinv := congrFun ((hcont p hp).fourierInv_fourier_eq hi hK) s
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  calc
    _ = f p s := (hcut p hp s hs).symm
    _ = _ := hinv.symm
    _ = ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [smul_eq_mul,fordAdditiveCharacter]
      have he : (↑(-2*Real.pi*ξ*(-s)) : ℂ)*Complex.I=
          2*(Real.pi:ℂ)*Complex.I*↑(ξ*s) := by push_cast; ring
      rw [he]
      exact mul_comm _ _

/-- Two bounded derivatives (of order zero and the decay order) suffice. -/
public theorem cutoff_family_fourier_decay_of_deriv_bounds {α : Type*} {P : Set α}
    (f : α → ℝ → ℂ) (j : ℕ)
    (hsm : ∀ p ∈ P, ContDiff ℝ ∞ (f p))
    (hsup : ∀ p ∈ P, tsupport (f p) ⊆ Icc (-2:ℝ) 2)
    (hb : ∃ D : ℝ, 1 ≤ D ∧ ∀ p ∈ P, ∀ x : ℝ, ∀ k ≤ j, ‖iteratedFDeriv ℝ k (f p) x‖ ≤ D) :
    ∃ D : ℝ, 0 < D ∧ ∀ p ∈ P, ∀ ξ : ℝ, (1+|ξ|)^j*‖𝓕 (f p) ξ‖ ≤ D := by
  obtain ⟨D,hD,hbound⟩ := hb
  refine ⟨(2:ℝ)^j*4*(D+D),by positivity,?_⟩
  intro p hp ξ
  have h := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order j
    (hsm p hp) (by norm_num : (-2:ℝ)≤2) ((subset_tsupport _).trans (hsup p hp))
    (zero_le_one.trans hD) (zero_le_one.trans hD)
    (fun x => by simpa only [← norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound p hp x 0 (Nat.zero_le j))
    (fun x => by simpa only [← norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound p hp x j le_rfl) ξ
  simpa only [show (2:ℝ)-(-2)=4 by norm_num] using h





end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025



end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025



end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

theorem exists_bourgainCubicQuartic_multiplier_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∃ K : ℝ → ℂ,
        Continuous K ∧ Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
        (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C ∧
        (∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) ∧
        ∀ s ∈ Icc (-1:ℝ) 1,
          fordAdditiveCharacter (a*s^3+b*s^4) =
            ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  let P := Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  let f := fun p : ℝ × ℝ => bourgainCubicQuarticCutoff p.1 p.2
  have hsm (p : ℝ × ℝ) (_ : p ∈ P) : ContDiff ℝ ∞ (f p) := bourgainCubicQuarticCutoff_smooth _ _
  have hs (p : ℝ × ℝ) (_ : p ∈ P) : tsupport (f p) ⊆ Icc (-2:ℝ) 2 := bourgainCubicQuarticCutoff_support _ _
  have hd := cutoff_family_fourier_decay_of_deriv_bounds f 102 hsm hs (by
    obtain ⟨D,hD,h⟩ := bourgainCubicQuarticCutoff_derivative_bound 102
    exact ⟨D,hD,fun p hp x k hk => h p.1 hp.1 p.2 hp.2 x k hk⟩)
  obtain ⟨C,hC,h⟩ := exists_cutoff_multiplier_kernel f (P:=P) (fun p s => p.1*s^3+p.2*s^4)
    (fun p hp => (hsm p hp).continuous)
    (fun p hp => isCompact_Icc.of_isClosed_subset isClosed_closure (hs p hp)) hd (by
      intro p hp s hs
      dsimp only [f,bourgainCubicQuarticCutoff]
      rw [modelPhaseBufferedCutoff_one (by norm_num)
        (by linarith [hs.1]) (by linarith [hs.2]),Complex.ofReal_one,one_mul])
  exact ⟨C,hC,fun a ha b hb => h (a,b) ⟨ha,hb⟩⟩

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  theorem weighted_integral_sixth_power
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {W f : α → ℝ}
    (hW : ∀ x, 0 ≤ W x)
    (hI : ∀ j ≤ 6, Integrable (fun x => W x*(f x)^j) μ) :
    (∫ x, W x*f x ∂μ)^6 ≤
      (∫ x, W x ∂μ)^5*(∫ x, W x*(f x)^6 ∂μ) := by
  let I := fun j : ℕ => ∫ x, W x*(f x)^j ∂μ
  have h0 : 0 ≤ I 0 := integral_nonneg (fun x => by simp [hW x])
  have h2 : 0 ≤ I 2 := integral_nonneg (fun x => mul_nonneg (hW x) (by positivity))
  have h6 : 0 ≤ I 6 := integral_nonneg (fun x => mul_nonneg (hW x) (by positivity))
  have h01 : (I 1)^2 ≤ I 0*I 2 := by
    simpa only [I,pow_zero,pow_one,one_pow,mul_one,one_mul] using
      (weighted_integral_cauchy_square (W:=W) (P:=fun _ => 1) (Q:=f) hW
        (by simpa using hI 0 (by omega))
        (by simpa using hI 1 (by omega))
        (hI 2 (by omega)))
  have h02 : (I 2)^2 ≤ I 0*I 4 := by
    have h := weighted_integral_cauchy_square (W:=W) (P:=fun _ => 1)
      (Q:=fun x => (f x)^2) hW
      (by simpa using hI 0 (by omega))
      (by simpa using hI 2 (by omega))
      (by simpa only [←pow_mul] using hI 4 (by omega))
    simpa only [I,pow_zero,one_pow,mul_one,one_mul,←pow_mul] using h
  have h24 : (I 4)^2 ≤ I 2*I 6 := by
    have hcross : Integrable (fun x => W x*f x*(f x)^3) μ := by
      convert hI 4 (by omega) using 1
      ext x
      ring
    have h := weighted_integral_cauchy_square (W:=W) (P:=f)
      (Q:=fun x => (f x)^3) hW (hI 2 (by omega)) hcross
      (by simpa only [←pow_mul] using hI 6 (by omega))
    have he (x : α) : W x*f x*(f x)^3 = W x*(f x)^4 := by ring
    simpa only [I,he,←pow_mul] using h
  have hcube : (I 2)^3 ≤ (I 0)^2*I 6 := by
    by_cases hz : I 2=0
    · simpa only [hz,zero_pow (by norm_num : (3:ℕ) ≠ 0)] using
        mul_nonneg (sq_nonneg (I 0)) h6
    have hpos : 0 < I 2 := lt_of_le_of_ne h2 (Ne.symm hz)
    have hs := pow_le_pow_left₀ (sq_nonneg (I 2)) h02 2
    have hs' : (I 2)^4 ≤ (I 0)^2*(I 4)^2 := by
      convert hs using 1 <;> ring
    have hprod := hs'.trans
      (mul_le_mul_of_nonneg_left h24 (sq_nonneg (I 0)))
    by_contra! hbad
    have hp := mul_pos hpos (sub_pos.mpr hbad)
    nlinarith only [hprod,hp]
  have hmain : (I 1)^6 ≤ (I 0)^5*I 6 := by
    calc
      _ = ((I 1)^2)^3 := by ring
      _ ≤ (I 0*I 2)^3 := pow_le_pow_left₀ (sq_nonneg (I 1)) h01 3
      _ = (I 0)^3*(I 2)^3 := mul_pow _ _ _
      _ ≤ (I 0)^3*((I 0)^2*I 6) :=
        mul_le_mul_of_nonneg_left hcube (pow_nonneg h0 3)
      _ = _ := by ring
  simpa only [I,pow_zero,pow_one,mul_one] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  theorem bourgainRemainderEnvelope_integrable :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) := by
  have hc : Continuous (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) :=
    (show Continuous (fun ξ : ℝ => (1+|ξ|)^102) from
      (continuous_const.add continuous_abs).pow 102).inv₀
      (fun ξ => ne_of_gt (by positivity : (0:ℝ) < (1+|ξ|)^102))
  apply integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hs : 1+ξ^2 ≤ (1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
  exact inv_anti₀ (by positivity) (hs.trans
    (pow_le_pow_right₀ (by linarith [abs_nonneg ξ]) (by omega : (2:ℕ) ≤ 102)))

theorem bourgain_finite_multiplier_moment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
    {K : ℝ → ℂ} (hKc : Continuous K)
    (hKi : Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖))
    {C : ℝ} (hC : 0 < C)
    (hmass : (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C)
    (henv : ∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) :
    ‖∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i))‖^6 ≤
      C^6*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  let F := fun ξ : ℝ => ∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)
  let M := ∑ i ∈ S, ‖z i‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hFc : Continuous F := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) : ‖F ξ‖ ≤ M := by
    calc
      _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (ξ*s i)‖ := norm_sum_le _ _
      _ = M := by simp only [M,norm_mul,sargos_character_norm,mul_one]
  have hweight (ξ : ℝ) : ‖K ξ‖ ≤ (1+|ξ|)^100*‖K ξ‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by linarith [abs_nonneg ξ]) : (1:ℝ) ≤ (1+|ξ|)^100)
      (norm_nonneg (K ξ))
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall hweight)
  have hJ (j : ℕ) : Integrable (fun ξ => ‖K ξ‖*‖F ξ‖^j) :=
    hK.norm.mul_bdd (hFc.norm.pow j).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ) j))
  have hV : Integrable (fun ξ => ((1+|ξ|)^102)⁻¹*‖F ξ‖^6) :=
    bourgainRemainderEnvelope_integrable.mul_bdd (hFc.norm.pow 6).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ) 6))
  have hmass' : (∫ ξ : ℝ, ‖K ξ‖) ≤ C :=
    (integral_mono hK.norm hKi hweight).trans hmass
  have hm0 : 0 ≤ ∫ ξ : ℝ, ‖K ξ‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hJ0 : 0 ≤ ∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6 :=
    integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (by positivity))
  have hpow := weighted_integral_sixth_power (W:=fun ξ => ‖K ξ‖)
    (f:=fun ξ => ‖F ξ‖) (fun _ => norm_nonneg _) (fun j _ => hJ j)
  have hmajor : (∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) ≤
      C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖F ξ‖^6) := by
    rw [←integral_const_mul]
    apply integral_mono (hJ 6) (hV.const_mul C)
    intro ξ
    simpa only [div_eq_mul_inv,mul_assoc] using
      mul_le_mul_of_nonneg_right (henv ξ) (pow_nonneg (norm_nonneg _) 6)
  calc
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖)^6 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 6
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun ξ => K ξ*F ξ)
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖)^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) := hpow
    _ ≤ C^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hmass' 5) hJ0
    _ ≤ C^5*(C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖F ξ‖^6)) :=
      mul_le_mul_of_nonneg_left hmajor (pow_nonneg hC.le 5)
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- A Fourier multiplier representation on the unit interval controls the
sixth moment of every finite exponential sum with that phase. -/
public theorem finite_moment_of_multiplier {ι : Type*} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
    (hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) (phase : ℝ → ℝ) {C : ℝ} (hC : 0 < C)
    {K : ℝ → ℂ} (hKc : Continuous K)
    (hKi : Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖))
    (hmass : (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C)
    (henv : ∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102)
    (hrep : ∀ x ∈ Icc (-1:ℝ) 1, fordAdditiveCharacter (phase x) =
      ∫ ξ : ℝ, K ξ * fordAdditiveCharacter (ξ*x)) :
    ‖∑ i ∈ S, z i*fordAdditiveCharacter (phase (s i))‖^6 ≤
      C^6*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  have hterm (i : ι) :
      Integrable (fun ξ : ℝ => z i*(K ξ*fordAdditiveCharacter (ξ*s i))) := by
    have hc : Continuous (fun ξ : ℝ => fordAdditiveCharacter (ξ*s i)) := by
      unfold fordAdditiveCharacter
      fun_prop
    exact (hK.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (sargos_character_norm (ξ*s i)).le))).const_mul _
  have he : (∑ i ∈ S, z i*fordAdditiveCharacter (phase (s i))) =
      ∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)) := by
    calc
      _ = ∑ i ∈ S, z i*(∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i)) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun v => z i*v) (hrep (s i) (hs i hi)))
      _ = ∑ i ∈ S, ∫ ξ : ℝ, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) := by
        simp only [integral_const_mul]
      _ = ∫ ξ : ℝ, ∑ i ∈ S, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) :=
        (integral_finsetSum S (fun i _ => hterm i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [he]
  exact bourgain_finite_multiplier_moment S z s hKc hKi hC hmass henv

theorem exists_bourgainCubicQuartic_finite_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (a*(s i)^3+b*(s i)^4)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  obtain ⟨C,hC,hkern⟩ := exists_bourgainCubicQuartic_multiplier_kernel
  refine ⟨C^6,by positivity,?_⟩
  intro a ha b hb ι S z s hs
  obtain ⟨K,hKc,hKi,hmass,henv,hrep⟩ := hkern a ha b hb
  exact finite_moment_of_multiplier S z s hs (fun x => a*x^3+b*x^4) hC hKc hKi hmass henv hrep

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem parabola_sum_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) (ξ α γ : ℝ) :
    sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*x i))
      x (fun i => (x i)^2) α γ =
    sargosPlanarSum S z x (fun i => (x i)^2) (α+ξ) γ := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

private theorem parabola_sourceWeight_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ)
    {R : ℝ} (hR : 0 < R) (r t ξ : ℝ) :
    (parabolaWeightedSixNorm
      (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
      S (fun i => z i*fordAdditiveCharacter (ξ*x i)) x)^2 ≤
      ((1+|ξ|/R)^100)^((3:ℝ)⁻¹)*
        (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) S z x)^2 := by
  let W := fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2
  let V := fun p : ℝ × ℝ => parabolaSourceWeight R r t (p.1-ξ) p.2
  have hW : Integrable W := integrable_parabolaSourceWeight hR r t
  have hV : Integrable V := by
    simpa only [V,W,Prod.fst_add,Prod.snd_add,add_zero,sub_eq_add_neg] using
      hW.comp_add_right (-ξ,0)
  have he := parabola_sum_modulation S z x ξ
  have hm :
      parabolaWeightedBilinearMoment W S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x =
      parabolaWeightedBilinearMoment V S S z z x x := by
    let F := fun p : ℝ × ℝ => V p*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^4
    calc
      _ = ∫ p : ℝ × ℝ, F (p+(ξ,0)) := by
        unfold parabolaWeightedBilinearMoment
        apply integral_congr_ae
        filter_upwards with p
        simp only [F,V,W,Prod.fst_add,Prod.snd_add,add_zero,add_sub_cancel_right,he]
      _ = ∫ p : ℝ × ℝ, F p := integral_add_right_eq_self F (ξ,0)
      _ = _ := rfl
  have hn :
      parabolaWeightedSixNorm W S (fun i => z i*fordAdditiveCharacter (ξ*x i)) x =
      parabolaWeightedSixNorm V S z x := by
    apply (pow_left_inj₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
      (parabolaWeightedSixNorm_nonneg _ _ _ _) (by norm_num : (6:ℕ) ≠ 0)).mp
    rw [parabolaWeightedSixNorm_pow_six W
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hW,
      parabolaWeightedSixNorm_pow_six V
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hV]
    exact hm
  change (parabolaWeightedSixNorm W S _ x)^2 ≤ _
  rw [hn]
  exact parabola_sixNorm_weight_comparison (by positivity)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hV hW
    (fun p => parabola_sourceWeight_horizontal_translate hR r t p.1 p.2 ξ) S z x

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u
private theorem bourgain_modulation_envelope {R : ℝ} (hR : 1 ≤ R) (ξ : ℝ) :
    ((1+|ξ|)^102)⁻¹*(1+|ξ|/R)^100 ≤ (1+ξ^2)⁻¹ := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdiv : |ξ|/R ≤ |ξ| := (div_le_self (abs_nonneg ξ) hR)
  have hloss : (1+|ξ|/R)^100 ≤ (1+|ξ|)^100 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 100
  have he : ((1+|ξ|)^102)⁻¹*(1+|ξ|)^100 = ((1+|ξ|)^2)⁻¹ := by
    rw [show (102:ℕ)=2+100 by omega,pow_add,mul_inv_rev]
    calc
      _ = ((1+|ξ|)^2)⁻¹*(((1+|ξ|)^100)⁻¹*(1+|ξ|)^100) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (by positivity),mul_one]
  calc
    _ ≤ ((1+|ξ|)^102)⁻¹*(1+|ξ|)^100 :=
      mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = ((1+|ξ|)^2)⁻¹ := he
    _ ≤ (1+ξ^2)⁻¹ := inv_anti₀ (by positivity)
      (by nlinarith [sq_abs ξ,abs_nonneg ξ])

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory
open scoped Matrix
namespace TaoTrudgianYang2025
private def bourgainQuadraticFrame (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,2*a,3*a^2,4*a^3;
     0,1,3*a,6*a^2;
     1,2*b,3*b^2,4*b^3;
     0,1,3*b,6*b^2]

private theorem bourgainQuadraticFrame_det (a b : ℝ) : (bourgainQuadraticFrame a b).det = 6*(b-a)^4 := by
  unfold bourgainQuadraticFrame
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,
    show (1:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (2:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (3:Fin 4).succAbove (2:Fin 3)=2 by decide]
  ring

private theorem bourgainQuadraticFrame_map_volume {a b : ℝ} (hab : a ≠ b) :
    Measure.map ((bourgainQuadraticFrame a b).mulVec)
      (volume : Measure (Fin 4 → ℝ)) =
      ENNReal.ofReal ((6*(b-a)^4)⁻¹) • volume := by
  have hn : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hp : 0 < 6*(b-a)^4 := by
    have h := sq_pos_of_ne_zero (pow_ne_zero 2 hn)
    nlinarith
  have hdet : (bourgainQuadraticFrame a b).det ≠ 0 := by
    rw [bourgainQuadraticFrame_det]
    exact hp.ne'
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  change Measure.map (bourgainQuadraticFrame a b).mulVec volume = _ at hm
  simpa only [bourgainQuadraticFrame_det,
    abs_of_pos (inv_pos.mpr hp)] using hm

private theorem bourgainQuadraticFrame_integral {a b : ℝ} (hab : a ≠ b)
    (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ x : Fin 4 → ℝ, f ((bourgainQuadraticFrame a b).mulVec x)) =
      (6*(b-a)^4)⁻¹*(∫ y : Fin 4 → ℝ, f y) := by
  have hc : Continuous ((bourgainQuadraticFrame a b).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hi := integral_map (μ:=volume) hc.aemeasurable hf.aestronglyMeasurable
  rw [bourgainQuadraticFrame_map_volume hab,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity),smul_eq_mul] at hi
  exact hi.symm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private def bourgainFourCoordinates :
    (Fin 4 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
        (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow))

private theorem bourgainFourCoordinates_apply (x : Fin 4 → ℝ) :
    bourgainFourCoordinates x = ((x 0,x 1),(x 2,x 3)) := rfl

private theorem bourgainFourCoordinates_measurePreserving :
    MeasurePreserving bourgainFourCoordinates volume volume := by
  exact ((volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)).comp
    ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
        (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm)

private theorem bourgainFourCoordinates_integral_product
    (f g : ℝ × ℝ → ℝ) :
    (∫ y : Fin 4 → ℝ, f (y 0,y 1)*g (y 2,y 3)) =
      (∫ p : ℝ × ℝ, f p)*(∫ q : ℝ × ℝ, g q) := by
  have h := bourgainFourCoordinates_measurePreserving.integral_comp
    bourgainFourCoordinates.measurableEmbedding
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1*g p.2)
  calc
    _ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), f p.1*g p.2 := by
      simpa only [bourgainFourCoordinates_apply] using h
    _ = _ := integral_prod_mul f g

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_cube_bound {a b R : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hR : 0 ≤ R)
    (x : Fin 4 → ℝ) (hx : ∀ j, |x j| ≤ R) :
    ∀ i, |(bourgainQuadraticFrame a b).mulVec x i| ≤ 10*R := by
  have ha2 : |a|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  have ha3 : |a|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  have hb2 : |b|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have hb3 : |b|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have hrow (i : Fin 4) : (∑ j, |bourgainQuadraticFrame a b i j|) ≤ 10 := by
    fin_cases i <;>
      norm_num [bourgainQuadraticFrame,Fin.sum_univ_succ,abs_mul,abs_pow] <;>
      nlinarith [sq_abs a,sq_abs b]
  intro i
  calc
    _ ≤ ∑ j, |bourgainQuadraticFrame a b i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |bourgainQuadraticFrame a b i j| *|x j| := by simp only [abs_mul]
    _ ≤ ∑ j, |bourgainQuadraticFrame a b i j| *R :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _ = (∑ j, |bourgainQuadraticFrame a b i j|)*R := (Finset.sum_mul _ _ _).symm
    _ ≤ 10*R := mul_le_mul_of_nonneg_right (hrow i) hR

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_box_product
    {a b R : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≠ b) (hR : 0 ≤ R)
    (f g : ℝ × ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ p, 0 ≤ g p) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f ((bourgainQuadraticFrame a b).mulVec x 0,
        (bourgainQuadraticFrame a b).mulVec x 1)*
      g ((bourgainQuadraticFrame a b).mulVec x 2,
        (bourgainQuadraticFrame a b).mulVec x 3)) ≤
      (6*(b-a)^4)⁻¹*
        (∫ p : ℝ × ℝ in Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R), f p)*
        (∫ q : ℝ × ℝ in Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R), g q) := by
  let B := Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R)
  let C := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  let F := (bourgainQuadraticFrame a b).mulVec
  let G := fun y : Fin 4 → ℝ => B.indicator f (y 0,y 1)*B.indicator g (y 2,y 3)
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hBcompact : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hi1 : Integrable (B.indicator f) :=
    (hf.continuousOn.integrableOn_compact hBcompact).integrable_indicator hB
  have hi2 : Integrable (B.indicator g) :=
    (hg.continuousOn.integrableOn_compact hBcompact).integrable_indicator hB
  have hGm : StronglyMeasurable G := by
    apply Measurable.stronglyMeasurable
    exact ((hf.measurable.indicator hB).comp (by fun_prop)).mul
      ((hg.measurable.indicator hB).comp (by fun_prop))
  have hiG : Integrable G := by
    have h := bourgainFourCoordinates_measurePreserving.integrable_comp_of_integrable
      (hi1.mul_prod hi2)
    simpa only [G,Function.comp_def,bourgainFourCoordinates_apply] using h
  have hFc : Continuous F := by
    change Continuous (Matrix.toLin' (bourgainQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hiGF : Integrable (fun x : Fin 4 → ℝ => G (F x)) := by
    have h : Integrable G (Measure.map F volume) := by
      rw [bourgainQuadraticFrame_map_volume hab]
      exact hiG.smul_measure ENNReal.ofReal_ne_top
    exact h.comp_measurable hFc.measurable
  have hG0 (y : Fin 4 → ℝ) : 0 ≤ G y := by
    apply mul_nonneg
    · exact Set.indicator_nonneg (fun p _ => hf0 p) _
    · exact Set.indicator_nonneg (fun p _ => hg0 p) _
  have he (x : Fin 4 → ℝ) (hx : x ∈ C) :
      f (F x 0,F x 1)*g (F x 2,F x 3) = G (F x) := by
    have hbound := bourgainQuadraticFrame_cube_bound ha hb hR x
      (fun j => abs_le.mpr ⟨hx.1 j,hx.2 j⟩)
    have hmem (i j : Fin 4) : (F x i,F x j) ∈ B := by
      exact ⟨⟨by linarith [(abs_le.mp (hbound i)).1],
        (abs_le.mp (hbound i)).2⟩,
        ⟨by linarith [(abs_le.mp (hbound j)).1],
        (abs_le.mp (hbound j)).2⟩⟩
    simp only [G,Set.indicator_of_mem (hmem 0 1),Set.indicator_of_mem (hmem 2 3)]
  calc
    _ = ∫ x : Fin 4 → ℝ in C, G (F x) :=
      setIntegral_congr_fun measurableSet_Icc he
    _ ≤ ∫ x : Fin 4 → ℝ, G (F x) :=
      setIntegral_le_integral hiGF (Filter.Eventually.of_forall (fun x => hG0 (F x)))
    _ = (6*(b-a)^4)⁻¹*(∫ y : Fin 4 → ℝ, G y) :=
      bourgainQuadraticFrame_integral hab G hGm
    _ = (6*(b-a)^4)⁻¹*((∫ p : ℝ × ℝ, B.indicator f p)*
        (∫ q : ℝ × ℝ, B.indicator g q)) := by
      rw [show (∫ y : Fin 4 → ℝ, G y) =
        (∫ p : ℝ × ℝ, B.indicator f p)*(∫ q : ℝ × ℝ, B.indicator g q) from
        bourgainFourCoordinates_integral_product (B.indicator f) (B.indicator g)]
    _ = _ := by rw [integral_indicator hB,integral_indicator hB]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuartic_remainder_bounds
    {c σ R : ℝ} (hc : |c| ≤ 1) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 ≤ R) (hsmall : 5*R*σ^3 ≤ 1)
    (x : Fin 4 → ℝ) (hx : ∀ j, |x j| ≤ R) :
    |(x 2+4*c*x 3)*σ^3| ≤ 1 ∧ |x 3*σ^4| ≤ 1 := by
  have hcprod : |c| *|x 3| ≤ R :=
    (mul_le_mul hc (hx 3) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hs : |x 2+4*c*x 3| ≤ 5*R := by
    have h := abs_add_le (x 2) (4*c*x 3)
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at h
    nlinarith [hx 2]
  constructor
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hσ 3)]
    exact (mul_le_mul_of_nonneg_right hs (pow_nonneg hσ 3)).trans hsmall
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hσ 4)]
    have hpow : σ^4 ≤ σ^3 := by
      have h := mul_le_mul_of_nonneg_left hσ1 (pow_nonneg hσ 3)
      nlinarith only [h]
    calc
      _ ≤ R*σ^4 := mul_le_mul_of_nonneg_right (hx 3) (pow_nonneg hσ 4)
      _ ≤ R*σ^3 := mul_le_mul_of_nonneg_left hpow hR
      _ ≤ 1 := by nlinarith [mul_nonneg hR (pow_nonneg hσ 3)]

universe u

theorem exists_bourgainQuartic_scaled_moment :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (c σ R : ℝ), |c| ≤ 1 → 0 ≤ σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      ∀ x : Fin 4 → ℝ, (∀ j, |x j| ≤ R) →
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+σ*s i)+x 1*(c+σ*s i)^2+
          x 2*(c+σ*s i)^3+x 3*(c+σ*s i)^4)‖^6 ≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            ((σ*s i)*(x 0+2*c*x 1+3*c^2*x 2+4*c^3*x 3)+
              (σ*s i)^2*(x 1+3*c*x 2+6*c^2*x 3)+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs c σ R hc hσ hσ1 hR hsmall x hx
  have hb := bourgainQuartic_remainder_bounds hc hσ hσ1 hR hsmall x hx
  let L := x 0+2*c*x 1+3*c^2*x 2+4*c^3*x 3
  let Q := x 1+3*c*x 2+6*c^2*x 3
  let A := (x 2+4*c*x 3)*σ^3
  let B := x 3*σ^4
  let Z := fun i => z i*fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q)
  have hmain := h A (abs_le.mp hb.1) B (abs_le.mp hb.2) S Z s hs
  have he :
      (∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+σ*s i)+x 1*(c+σ*s i)^2+
          x 2*(c+σ*s i)^3+x 3*(c+σ*s i)^4)) =
      fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
        ∑ i ∈ S, Z i*fordAdditiveCharacter (A*(s i)^3+B*(s i)^4) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Z]
    rw [show fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
        ((z i*fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q))*
          fordAdditiveCharacter (A*(s i)^3+B*(s i)^4)) =
        z i*(fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
          (fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q)*
            fordAdditiveCharacter (A*(s i)^3+B*(s i)^4))) by ring]
    rw [←fordAdditiveCharacter_add,←fordAdditiveCharacter_add]
    congr 2
    dsimp [L,Q,A,B]
    ring
  rw [he,norm_mul,sargos_character_norm,one_mul]
  have hr (ξ : ℝ) :
      (∑ i ∈ S, Z i*fordAdditiveCharacter (ξ*s i)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((σ*s i)*L+(σ*s i)^2*Q+ξ*s i) := by
    simp only [Z,mul_assoc,←fordAdditiveCharacter_add]
  simpa only [hr,L,Q] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_finite_product {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (u : ι → ℝ) (v : τ → ℝ) {a b R : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≠ b) (hR : 0 ≤ R) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      ‖sargosPlanarSum S z u (fun i => (u i)^2)
        ((bourgainQuadraticFrame a b).mulVec x 0)
        ((bourgainQuadraticFrame a b).mulVec x 1)‖^6*
      ‖sargosPlanarSum V c v (fun j => (v j)^2)
        ((bourgainQuadraticFrame a b).mulVec x 2)
        ((bourgainQuadraticFrame a b).mulVec x 3)‖^6) ≤
      (6*(b-a)^4)⁻¹*
        parabolaBoxBilinearMoment S S z z u u (10*R) 0 0*
        parabolaBoxBilinearMoment V V c c v v (10*R) 0 0 := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum S z u (fun i => (u i)^2) p.1 p.2‖^6) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hg : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum V c v (fun j => (v j)^2) p.1 p.2‖^6) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have h := bourgainQuadraticFrame_box_product ha hb hab hR
    (fun p => ‖sargosPlanarSum S z u (fun i => (u i)^2) p.1 p.2‖^6)
    (fun p => ‖sargosPlanarSum V c v (fun j => (v j)^2) p.1 p.2‖^6)
    hf hg (fun _ => by positivity) (fun _ => by positivity)
  have he (w : ℝ) : w^2*w^4=w^6 := by ring
  simpa only [parabolaBoxBilinearMoment,he,zero_sub,zero_add,neg_mul] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem integrable_bourgain_modulated_box {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s u : ι → ℝ) (R r t : ℝ) :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹*
      parabolaBoxBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*s i))
        (fun i => z i*fordAdditiveCharacter (ξ*s i)) u u R r t) := by
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  let F := fun (ξ : ℝ) (p : ℝ × ℝ) =>
    ‖sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
      u (fun i => (u i)^2) p.1 p.2‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  have hFc : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2) := by
    unfold F sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) (p : ℝ × ℝ) :
      ‖F ξ p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 6
    have h := norm_sargosPlanarSum_le_sum_norm S
      (fun i => z i*fordAdditiveCharacter (ξ*s i))
      u (fun i => (u i)^2) p.1 p.2
    simpa only [norm_mul,sargos_character_norm,mul_one] using h
  have hiV : Integrable V := bourgainRemainderEnvelope_integrable
  have hiF : Integrable (fun q : ℝ × (ℝ × ℝ) => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict B)) := by
    have hiConst : IntegrableOn (fun _p : ℝ × ℝ => (1:ℝ)) B :=
      integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
    have hprod := hiV.mul_prod hiConst
    have h := hprod.mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using h
  have he (w : ℝ) : w^2*w^4=w^6 := by ring
  simpa only [integral_const_mul,F,V,B,parabolaBoxBilinearMoment,he] using
    hiF.integral_prod_left

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

public  theorem bourgain_character_six_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (θ : ι → ℝ) :
    ‖(‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖^6:ℝ)‖ ≤
      (∑ i ∈ S, ‖z i‖)^6 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 6
  calc
    _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (θ i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]

private theorem bourgain_frame_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (σ ξ α γ : ℝ) :
    sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
      (fun i => σ*s i) (fun i => (σ*s i)^2) α γ =
    ∑ i ∈ S, z i*fordAdditiveCharacter
      ((σ*s i)*α+(σ*s i)^2*γ+ξ*s i) := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

private theorem bourgainQuadraticFrame_apply (a b : ℝ) (x : Fin 4 → ℝ) :
    (bourgainQuadraticFrame a b).mulVec x =
      ![x 0+2*a*x 1+3*a^2*x 2+4*a^3*x 3,
        x 1+3*a*x 2+6*a^2*x 3,
        x 0+2*b*x 1+3*b^2*x 2+4*b^3*x 3,
        x 1+3*b*x 2+6*b^2*x 3] := by
  funext i
  fin_cases i <;>
    simp [bourgainQuadraticFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

public  theorem bourgain_kernel_setIntegral_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {B : Set α} {f : α → ℝ} {H : β → α → ℝ} {C : ℝ}
    (hB : MeasurableSet B) (hf : IntegrableOn f B μ)
    (hH : Integrable (Function.uncurry H) (ν.prod (μ.restrict B)))
    (hp : ∀ x ∈ B, f x ≤ C*(∫ y, H y x ∂ν)) :
    (∫ x in B, f x ∂μ) ≤ C*(∫ y, ∫ x in B, H y x ∂μ ∂ν) := by
  have h := setIntegral_mono_on hf (hH.integral_prod_right.const_mul C) hB hp
  rw [integral_const_mul] at h
  dsimp only [Function.uncurry] at h
  have hswap := integral_integral_swap (μ:=ν) (ν:=μ.restrict B) hH
  rw [←hswap] at h
  exact h

universe u
set_option maxHeartbeats 400000 in

theorem exists_bourgainQuartic_bilinear_reduction :
    ∃ C > (0:ℝ), ∀ (ι τ : Type u) (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (s : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      (∀ j ∈ V, v j ∈ Icc (-1:ℝ) 1) →
      ∀ (a b σ R : ℝ), |a| ≤ 1 → |b| ≤ 1 → a ≠ b →
      0 ≤ σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*(a+σ*s i)+x 1*(a+σ*s i)^2+
            x 2*(a+σ*s i)^3+x 3*(a+σ*s i)^4)‖^6*
        ‖∑ j ∈ V, c j*fordAdditiveCharacter
          (x 0*(b+σ*v j)+x 1*(b+σ*v j)^2+
            x 2*(b+σ*v j)^3+x 3*(b+σ*v j)^4)‖^6) ≤
        C*(6*(b-a)^4)⁻¹*
          (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            parabolaBoxBilinearMoment S S
              (fun i => z i*fordAdditiveCharacter (ξ*s i))
              (fun i => z i*fordAdditiveCharacter (ξ*s i))
              (fun i => σ*s i) (fun i => σ*s i) (10*R) 0 0)*
          (∫ η : ℝ, ((1+|η|)^102)⁻¹*
            parabolaBoxBilinearMoment V V
              (fun j => c j*fordAdditiveCharacter (η*v j))
              (fun j => c j*fordAdditiveCharacter (η*v j))
              (fun j => σ*v j) (fun j => σ*v j) (10*R) 0 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainQuartic_scaled_moment.{u}
  refine ⟨C^2,by positivity,?_⟩
  intro ι τ S V z c s v hs hv a b σ R ha hb hab hσ hσ1 hR hsmall
  let B := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let A := fun x : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*(a+σ*s i)+x 1*(a+σ*s i)^2+x 2*(a+σ*s i)^3+x 3*(a+σ*s i)^4)‖^6
  let D := fun x : Fin 4 → ℝ => ‖∑ j ∈ V, c j*fordAdditiveCharacter
    (x 0*(b+σ*v j)+x 1*(b+σ*v j)^2+x 2*(b+σ*v j)^3+x 3*(b+σ*v j)^4)‖^6
  let F := fun (ξ : ℝ) (x : Fin 4 → ℝ) =>
    ‖∑ i ∈ S, z i*fordAdditiveCharacter
      ((σ*s i)*(x 0+2*a*x 1+3*a^2*x 2+4*a^3*x 3)+
        (σ*s i)^2*(x 1+3*a*x 2+6*a^2*x 3)+ξ*s i)‖^6
  let G := fun (η : ℝ) (x : Fin 4 → ℝ) =>
    ‖∑ j ∈ V, c j*fordAdditiveCharacter
      ((σ*v j)*(x 0+2*b*x 1+3*b^2*x 2+4*b^3*x 3)+
        (σ*v j)^2*(x 1+3*b*x 2+6*b^2*x 3)+η*v j)‖^6
  let J := fun ξ : ℝ => parabolaBoxBilinearMoment S S
    (fun i => z i*fordAdditiveCharacter (ξ*s i))
    (fun i => z i*fordAdditiveCharacter (ξ*s i))
    (fun i => σ*s i) (fun i => σ*s i) (10*R) 0 0
  let K := fun η : ℝ => parabolaBoxBilinearMoment V V
    (fun j => c j*fordAdditiveCharacter (η*v j))
    (fun j => c j*fordAdditiveCharacter (η*v j))
    (fun j => σ*v j) (fun j => σ*v j) (10*R) 0 0
  have hF0 (ξ : ℝ) (x : Fin 4 → ℝ) : 0 ≤ F ξ x := by dsimp [F]; positivity
  have hG0 (η : ℝ) (x : Fin 4 → ℝ) : 0 ≤ G η x := by dsimp [G]; positivity
  have hcont : Continuous (fun qx : (ℝ × ℝ) × (Fin 4 → ℝ) =>
      F qx.1.1 qx.2*G qx.1.2 qx.2) := by
    unfold F G fordAdditiveCharacter
    fun_prop
  have hfinite (qx : (ℝ × ℝ) × (Fin 4 → ℝ)) :
      ‖F qx.1.1 qx.2*G qx.1.2 qx.2‖ ≤
        (∑ i ∈ S, ‖z i‖)^6*(∑ j ∈ V, ‖c j‖)^6 := by
    rw [norm_mul]
    exact mul_le_mul (bourgain_character_six_bound S z _)
      (bourgain_character_six_bound V c _) (norm_nonneg _) (by positivity)
  have hW : Integrable W := bourgainRemainderEnvelope_integrable
  have hiH : Integrable (fun qx : (ℝ × ℝ) × (Fin 4 → ℝ) =>
      W qx.1.1*W qx.1.2*(F qx.1.1 qx.2*G qx.1.2 qx.2))
      (volume.prod (volume.restrict B)) := by
    have hconst : IntegrableOn (fun _x : Fin 4 → ℝ => (1:ℝ)) B :=
      integrableOn_const isCompact_Icc.measure_ne_top
    have hprod := (hW.mul_prod hW).mul_prod hconst
    have h := hprod.mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hfinite)
    convert h using 1
    funext qx
    simp only [mul_one]
  have hAD : IntegrableOn (fun x => A x*D x) B := by
    have hc : Continuous (fun x => A x*D x) := by
      unfold A D fordAdditiveCharacter
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (x : Fin 4 → ℝ) (hx : x ∈ B) :
      A x*D x ≤ C^2*(∫ q : ℝ × ℝ, W q.1*W q.2*(F q.1 x*G q.2 x)) := by
    have hxc : ∀ j, |x j| ≤ R := fun j => abs_le.mpr ⟨hx.1 j,hx.2 j⟩
    have hA := hbound S z s hs a σ R ha hσ hσ1 hR hsmall x hxc
    have hD := hbound V c v hv b σ R hb hσ hσ1 hR hsmall x hxc
    have hpos : 0 ≤ C*(∫ ξ : ℝ, W ξ*F ξ x) :=
      mul_nonneg hC.le (integral_nonneg (fun ξ => mul_nonneg (by dsimp [W]; positivity) (hF0 ξ x)))
    have hprod := mul_le_mul hA hD (by positivity) hpos
    have he : (∫ q : ℝ × ℝ, W q.1*W q.2*(F q.1 x*G q.2 x)) =
        (∫ ξ : ℝ, W ξ*F ξ x)*(∫ η : ℝ, W η*G η x) := by
      calc
        _ = ∫ q : ℝ × ℝ, (W q.1*F q.1 x)*(W q.2*G q.2 x) := by
          apply integral_congr_ae
          filter_upwards with q
          ring
        _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
          (fun ξ : ℝ => W ξ*F ξ x) (fun η : ℝ => W η*G η x)
    rw [he]
    calc
      _ ≤ (C*(∫ ξ : ℝ, W ξ*F ξ x))*(C*(∫ η : ℝ, W η*G η x)) := hprod
      _ = _ := by ring
  have hm := bourgain_kernel_setIntegral_bound (α:=Fin 4 → ℝ) (β:=ℝ × ℝ)
    (μ:=volume) (ν:=volume) (B:=B) (C:=C^2)
    (f:=fun x => A x*D x)
    (H:=fun q x => W q.1*W q.2*(F q.1 x*G q.2 x))
    measurableSet_Icc hAD hiH hpoint
  have hFframe (ξ : ℝ) (x : Fin 4 → ℝ) :
      F ξ x = ‖sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
        (fun i => σ*s i) (fun i => (σ*s i)^2)
        ((bourgainQuadraticFrame a b).mulVec x 0)
        ((bourgainQuadraticFrame a b).mulVec x 1)‖^6 := by
    rw [bourgain_frame_modulation,bourgainQuadraticFrame_apply]
    rfl
  have hGframe (η : ℝ) (x : Fin 4 → ℝ) :
      G η x = ‖sargosPlanarSum V (fun j => c j*fordAdditiveCharacter (η*v j))
        (fun j => σ*v j) (fun j => (σ*v j)^2)
        ((bourgainQuadraticFrame a b).mulVec x 2)
        ((bourgainQuadraticFrame a b).mulVec x 3)‖^6 := by
    rw [bourgain_frame_modulation,bourgainQuadraticFrame_apply]
    rfl
  have hinner (q : ℝ × ℝ) :
      (∫ x : Fin 4 → ℝ in B, F q.1 x*G q.2 x) ≤
        (6*(b-a)^4)⁻¹*J q.1*K q.2 := by
    simpa only [hFframe,hGframe,J,K,B] using
      bourgainQuadraticFrame_finite_product S V
        (fun i => z i*fordAdditiveCharacter (q.1*s i))
        (fun j => c j*fordAdditiveCharacter (q.2*v j))
        (fun i => σ*s i) (fun j => σ*v j) ha hb hab hR
  have hJ : Integrable (fun ξ => W ξ*J ξ) :=
    integrable_bourgain_modulated_box S z s (fun i => σ*s i) (10*R) 0 0
  have hK : Integrable (fun η => W η*K η) :=
    integrable_bourgain_modulated_box V c v (fun j => σ*v j) (10*R) 0 0
  have hmajor := integral_mono hiH.integral_prod_left
    ((hJ.mul_prod hK).const_mul ((6*(b-a)^4)⁻¹)) (fun q => by
      dsimp only [Prod.fst,Prod.snd]
      rw [integral_const_mul]
      calc
        _ ≤ (W q.1*W q.2)*((6*(b-a)^4)⁻¹*J q.1*K q.2) :=
          mul_le_mul_of_nonneg_left (hinner q) (by dsimp [W]; positivity)
        _ = _ := by ring)
  rw [integral_const_mul] at hmajor
  have heProduct : (∫ q : ℝ × ℝ, (W q.1*J q.1)*(W q.2*K q.2)) =
      (∫ ξ : ℝ, W ξ*J ξ)*(∫ η : ℝ, W η*K η) :=
    integral_prod_mul (μ:=volume) (ν:=volume)
      (fun ξ : ℝ => W ξ*J ξ) (fun η : ℝ => W η*K η)
  rw [heProduct] at hmajor
  calc
    _ ≤ C^2*(∫ q : ℝ × ℝ, ∫ x : Fin 4 → ℝ in B,
        W q.1*W q.2*(F q.1 x*G q.2 x)) := hm
    _ ≤ C^2*((6*(b-a)^4)⁻¹*
        ((∫ ξ : ℝ, W ξ*J ξ)*(∫ η : ℝ, W η*K η))) :=
      mul_le_mul_of_nonneg_left hmajor (sq_nonneg C)
    _ = _ := by dsimp [W,J,K]; ring

end TaoTrudgianYang2025

noncomputable section
namespace TaoTrudgianYang2025

public  theorem bourgain_source_quartic_phase {t : ℝ} (ht : 0 ≤ t) (x : Fin 4 → ℝ) :
    x 0*t+x 1*t^2+x 2*t^((3:ℝ)/2)+x 3*Real.sqrt t =
      x 3*Real.sqrt t+x 0*(Real.sqrt t)^2+
        x 2*(Real.sqrt t)^3+x 1*(Real.sqrt t)^4 := by
  have h3 : (Real.sqrt t)^3 = t^((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul ht]
    congr 1
    norm_num
  have h4 : (Real.sqrt t)^4 = t^2 := by
    calc
      _ = ((Real.sqrt t)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt ht]
  rw [Real.sq_sqrt ht,h3,h4]
  ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

public  def bourgainSourcePermutation : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    ((Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 1 3))

private theorem bourgainSourcePermutation_apply (x : Fin 4 → ℝ) :
    bourgainSourcePermutation x = ![x 3,x 0,x 2,x 1] := by
  funext i
  fin_cases i <;> rfl

public  theorem bourgainSourcePermutation_measurePreserving :
    MeasurePreserving bourgainSourcePermutation volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
    ((Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 1 3))

private theorem bourgainSourcePermutation_preimage_cube (R : ℝ) :
    bourgainSourcePermutation ⁻¹' Icc (fun _ => -R) (fun _ => R) =
      Icc (fun _ => -R) (fun _ => R) := by
  ext x
  change ((∀ i, -R ≤ bourgainSourcePermutation x i) ∧
    ∀ i, bourgainSourcePermutation x i ≤ R) ↔
    ((∀ i, -R ≤ x i) ∧ ∀ i, x i ≤ R)
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> intro i <;> fin_cases i <;>
    first | exact h1 0 | exact h1 1 | exact h1 2 | exact h1 3 |
      exact h2 0 | exact h2 1 | exact h2 2 | exact h2 3

private theorem bourgainSourcePermutation_cube_integral (R : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f (bourgainSourcePermutation x)) =
    ∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f y := by
  let B := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  have h := bourgainSourcePermutation_measurePreserving.integral_comp
    bourgainSourcePermutation.measurableEmbedding (B.indicator f)
  rw [integral_indicator measurableSet_Icc] at h
  have he (x : Fin 4 → ℝ) :
      B.indicator f (bourgainSourcePermutation x) =
        B.indicator (fun y => f (bourgainSourcePermutation y)) x := by
    have hx : bourgainSourcePermutation x ∈ B ↔ x ∈ B := by
      change x ∈ bourgainSourcePermutation ⁻¹' B ↔ x ∈ B
      rw [bourgainSourcePermutation_preimage_cube]
    by_cases hmem : x ∈ B
    · rw [indicator_of_mem hmem,indicator_of_mem (hx.mpr hmem)]
    · rw [indicator_of_notMem hmem,indicator_of_notMem (mt hx.mp hmem)]
  simp_rw [he] at h
  rw [integral_indicator measurableSet_Icc] at h
  exact h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

theorem exists_bourgainSourceCurve_bilinear_reduction :
    ∃ C > (0:ℝ), ∀ (ι τ : Type u) (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
      ∀ (a b σ R : ℝ), |a| ≤ 1 → |b| ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      (∀ i ∈ S, |Real.sqrt (w i)-a| ≤ σ) →
      (∀ j ∈ V, |Real.sqrt (v j)-b| ≤ σ) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6*
        ‖∑ j ∈ V, c j*fordAdditiveCharacter
          (x 0*v j+x 1*(v j)^2+x 2*(v j)^((3:ℝ)/2)+x 3*Real.sqrt (v j))‖^6) ≤
        C*(6*(b-a)^4)⁻¹*
          (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            parabolaBoxBilinearMoment S S
              (fun i => z i*fordAdditiveCharacter (ξ*((Real.sqrt (w i)-a)/σ)))
              (fun i => z i*fordAdditiveCharacter (ξ*((Real.sqrt (w i)-a)/σ)))
              (fun i => Real.sqrt (w i)-a) (fun i => Real.sqrt (w i)-a) (10*R) 0 0)*
          (∫ η : ℝ, ((1+|η|)^102)⁻¹*
            parabolaBoxBilinearMoment V V
              (fun j => c j*fordAdditiveCharacter (η*((Real.sqrt (v j)-b)/σ)))
              (fun j => c j*fordAdditiveCharacter (η*((Real.sqrt (v j)-b)/σ)))
              (fun j => Real.sqrt (v j)-b) (fun j => Real.sqrt (v j)-b) (10*R) 0 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainQuartic_bilinear_reduction.{u}
  refine ⟨C,hC,?_⟩
  intro ι τ S V z c w v hw hv a b σ R ha hb hab hσ hσ1 hR hsmall hwc hvc
  let s := fun i => (Real.sqrt (w i)-a)/σ
  let t := fun j => (Real.sqrt (v j)-b)/σ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    apply abs_le.mp
    dsimp [s]
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hwc i hi)
  have ht : ∀ j ∈ V, t j ∈ Icc (-1:ℝ) 1 := by
    intro j hj
    apply abs_le.mp
    dsimp [t]
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hvc j hj)
  have hsbase (i : ι) : σ*s i = Real.sqrt (w i)-a := by
    dsimp [s]
    field_simp
  have htbase (j : τ) : σ*t j = Real.sqrt (v j)-b := by
    dsimp [t]
    field_simp
  have hscenter (i : ι) : a+σ*s i = Real.sqrt (w i) := by rw [hsbase]; ring
  have htcenter (j : τ) : b+σ*t j = Real.sqrt (v j) := by rw [htbase]; ring
  let QS := fun y : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (y 0*(a+σ*s i)+y 1*(a+σ*s i)^2+y 2*(a+σ*s i)^3+y 3*(a+σ*s i)^4)‖^6
  let QV := fun y : Fin 4 → ℝ => ‖∑ j ∈ V, c j*fordAdditiveCharacter
    (y 0*(b+σ*t j)+y 1*(b+σ*t j)^2+y 2*(b+σ*t j)^3+y 3*(b+σ*t j)^4)‖^6
  have heS (x : Fin 4 → ℝ) :
      (∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((bourgainSourcePermutation x) 0*(a+σ*s i)+
          (bourgainSourcePermutation x) 1*(a+σ*s i)^2+
          (bourgainSourcePermutation x) 2*(a+σ*s i)^3+
          (bourgainSourcePermutation x) 3*(a+σ*s i)^4) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hscenter,bourgainSourcePermutation_apply]
    exact congrArg (fun q => z i*fordAdditiveCharacter q)
      (bourgain_source_quartic_phase (hw i hi) x)
  have heV (x : Fin 4 → ℝ) :
      (∑ j ∈ V, c j*fordAdditiveCharacter
        (x 0*v j+x 1*(v j)^2+x 2*(v j)^((3:ℝ)/2)+x 3*Real.sqrt (v j))) =
      ∑ j ∈ V, c j*fordAdditiveCharacter
        ((bourgainSourcePermutation x) 0*(b+σ*t j)+
          (bourgainSourcePermutation x) 1*(b+σ*t j)^2+
          (bourgainSourcePermutation x) 2*(b+σ*t j)^3+
          (bourgainSourcePermutation x) 3*(b+σ*t j)^4) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [htcenter,bourgainSourcePermutation_apply]
    exact congrArg (fun q => c j*fordAdditiveCharacter q)
      (bourgain_source_quartic_phase (hv j hj) x)
  have hmain := hbound ι τ S V z c s t hs ht a b σ R ha hb hab hσ.le hσ1 hR hsmall
  calc
    _ = ∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        QS (bourgainSourcePermutation x)*QV (bourgainSourcePermutation x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [heS,heV]
    _ = ∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), QS y*QV y :=
      bourgainSourcePermutation_cube_integral R (fun y => QS y*QV y)
    _ ≤ _ := by
      simpa only [QS,QV,hsbase,htbase,s,t] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_parabolaBox_scaled_rapid_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 0 < R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := LogarithmicSixth.exists_logCurveDecouplingBound_dyadic.{u}
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : ParabolaWeightBand (σ/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaRapidWeight_band hR hwidth r t
  have hWlog : LogarithmicSixth.LogCurveWeightBand 0 (σ/((2^n:ℕ):ℝ)) W := by
    simpa only [ParabolaWeightBand, LogarithmicSixth.LogCurveWeightBand,
      LogarithmicSixth.logCurveBandGauge, add_zero, one_pow, div_one, one_mul] using hW
  have hnormLog := (hD n).rescale (κ:=0) (by norm_num) hσ (a:=0) (by norm_num)
    (by simpa using hσ₁) ι W hWlog S z x (by simpa only [zero_add] using hx)
  have hnorm := hnormLog
  simp only [LogarithmicSixth.logCurveWeightedSixNorm, LogarithmicSixth.logCurve_zero] at hnorm
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hbox := parabolaBox_le_rapid (Finset.univ.sigma S) (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t
  have hid := parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have he : parabolaRapidBilinearMoment
      (Finset.univ.sigma S) (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t =
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^6 := by
    simpa only [parabolaRapidBilinearMoment,parabolaWeightedBilinearMoment,W] using hid.symm
  exact hbox.trans (he.le.trans hcube)

private theorem exists_parabolaBox_scaled_source_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 0 < R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨C,hC,hbox⟩ := exists_parabolaBox_scaled_rapid_decoupling.{u} hε
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨C*K,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  have hm := hbox n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  have hnorm (j : Fin (2^n)) :=
    parabola_sixNorm_weight_comparison hK.le
      (fun p : ℝ × ℝ => parabolaRapidWeight_nonneg R r t p.1 p.2)
      (fun p : ℝ × ℝ => parabolaSourceWeight_nonneg R r t p.1 p.2)
      (parabolaRapidWeight_band hR hwidth r t).2.1
      (integrable_parabolaSourceWeight hR r t)
      (fun p => hcomp R r t p.1 p.2) (S j) (z j) (x j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hs
  have hcube := pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
  rw [mul_pow] at hcube
  have hroot := Real.rpow_inv_natCast_pow hK.le (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot] at hcube
  calc
    _ ≤ _ := hm
    _ ≤ C*(2:ℝ)^(ε*n)*(K*
        (∑ j, (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
          (S j) (z j) (x j))^2)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

theorem exists_parabolaBox_scaled_modulation_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 1 ≤ σ*R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (s : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, s j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
            (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
            (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
            (fun jk => σ*s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t) ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (fun i => σ*s j i))^2)^3 := by
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_scaled_source_decoupling.{u} hε
  refine ⟨D*Real.pi,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hσR hwidth ι S z s hs
  have hR : 0 < R := (mul_pos_iff_of_pos_left hσ).mp (lt_of_lt_of_le zero_lt_one hσR)
  let Q := ∑ j, (parabolaWeightedSixNorm
    (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
    (S j) (z j) (fun i => σ*s j i))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : ∀ j, ∀ k ∈ S j, σ*s j k ∈ Icc
      (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ))) := by
    intro j k hk
    exact ⟨mul_le_mul_of_nonneg_left (hs j k hk).1 hσ.le,
      mul_le_mul_of_nonneg_left (hs j k hk).2 hσ.le⟩
  have hpoint (ξ : ℝ) :
      parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
        (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
        (fun jk => σ*s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t ≤
        D*(2:ℝ)^(ε*n)*(1+|ξ|/(σ*R))^100*Q^3 := by
    have hd := hdec n σ R r t hσ hσ₁ hR hwidth ι S
      (fun j i => z j i*fordAdditiveCharacter (ξ*s j i)) (fun j i => σ*s j i) hx
    have hmod (v : ℝ) : (ξ/σ)*(σ*v) = ξ*v := by field_simp
    have hratio : |ξ/σ|/R = |ξ|/(σ*R) := by rw [abs_div,abs_of_pos hσ,div_div]
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
      parabola_sourceWeight_modulation (S j) (z j) (fun i => σ*s j i) hR r t (ξ/σ))
    simp_rw [hmod,hratio] at hsum
    rw [←Finset.mul_sum] at hsum
    have hc := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hsum 3
    rw [mul_pow] at hc
    have hroot := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/(σ*R))^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hroot
    rw [hroot] at hc
    calc
      _ ≤ _ := hd
      _ ≤ D*(2:ℝ)^(ε*n)*((1+|ξ|/(σ*R))^100*Q^3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have hi := integrable_bourgain_modulated_box (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t
  have hj := integrable_inv_one_add_sq.const_mul (D*(2:ℝ)^(ε*n)*Q^3)
  have hm := integral_mono hi hj (fun ξ => by
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(D*(2:ℝ)^(ε*n)*(1+|ξ|/(σ*R))^100*Q^3) :=
        mul_le_mul_of_nonneg_left (hpoint ξ) (by positivity)
      _ = D*(2:ℝ)^(ε*n)*Q^3*(((1+|ξ|)^102)⁻¹*(1+|ξ|/(σ*R))^100) := by ring
      _ ≤ D*(2:ℝ)^(ε*n)*Q^3*(1+ξ^2)⁻¹ :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope hσR ξ) (by positivity))
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hm
  calc
    _ ≤ _ := hm
    _ = _ := by dsimp [Q]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

theorem exists_bourgainSourceCurve_parabolic_cell_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (a b σ R : ℝ),
      |a| ≤ 1 → |b| ≤ 1 → a ≠ b → 0 < σ → σ ≤ 1 → 0 ≤ R →
      5*R*σ^3 ≤ 1 → 1 ≤ σ*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
              x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
          ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
            (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
              x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
          C*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (S j) (z j) (fun i => Real.sqrt (w j i)-a))^2)^3*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (V j) (c j) (fun k => Real.sqrt (v j k)-b))^2)^3 := by
  obtain ⟨E,hE,hsource⟩ := exists_bourgainSourceCurve_bilinear_reduction.{u}
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_scaled_modulation_decoupling.{u}
    (ε:=ε/2) (by positivity)
  refine ⟨E*D^2,by positivity,?_⟩
  intro n a b σ R ha hb hab hσ hσ₁ hR hrem hσR hwidth ι τ S V z c w v hw hv hwgrid hvgrid
  let s := fun j i => (Real.sqrt (w j i)-a)/σ
  let t := fun j k => (Real.sqrt (v j k)-b)/σ
  have hsbase (j : Fin (2^n)) (i : ι) : σ*s j i = Real.sqrt (w j i)-a := by
    dsimp [s]
    field_simp
  have htbase (j : Fin (2^n)) (k : τ) : σ*t j k = Real.sqrt (v j k)-b := by
    dsimp [t]
    field_simp
  have hsgrid : ∀ j, ∀ i ∈ S j, s j i ∈ Icc
      ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    intro j i hi
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hwgrid j i hi).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hwgrid j i hi).2]
  have htgrid : ∀ j, ∀ k ∈ V j, t j k ∈ Icc
      ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    intro j k hk
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hvgrid j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hvgrid j k hk).2]
  have hunit (j : Fin (2^n)) {y : ℝ}
      (hy : y ∈ Icc ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      y ∈ Icc (0:ℝ) 1 := by
    have hl : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ) := by positivity
    have hh : ((j:ℕ)+1:ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast (show (j:ℕ)+1 ≤ 2^n from j.isLt)
    exact ⟨hl.trans hy.1,hy.2.trans hh⟩
  have hwindowS : ∀ ji ∈ Finset.univ.sigma S, |Real.sqrt (w ji.1 ji.2)-a| ≤ σ := by
    intro ji hji
    have hh := hunit ji.1 (hsgrid ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    rw [←hsbase,abs_of_nonneg (mul_nonneg hσ.le hh.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hσ.le
  have hwindowV : ∀ jk ∈ Finset.univ.sigma V, |Real.sqrt (v jk.1 jk.2)-b| ≤ σ := by
    intro jk hjk
    have hh := hunit jk.1 (htgrid jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    rw [←htbase,abs_of_nonneg (mul_nonneg hσ.le hh.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hσ.le
  have hmain := hsource ((j : Fin (2^n)) × ι) ((j : Fin (2^n)) × τ)
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun jk => c jk.1 jk.2)
    (fun ji => w ji.1 ji.2) (fun jk => v jk.1 jk.2)
    (fun ji hji => hw ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => hv jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    a b σ R ha hb hab hσ hσ₁ hR hrem hwindowS hwindowV
  have hS := hdec n σ (10*R) 0 0 hσ hσ₁ hσR hwidth ι S z s hsgrid
  have hV := hdec n σ (10*R) 0 0 hσ hσ₁ hσR hwidth τ V c t htgrid
  simp_rw [hsbase] at hS
  simp_rw [htbase] at hV
  have hnonnegV : 0 ≤ ∫ η : ℝ, ((1+|η|)^102)⁻¹*
      parabolaBoxBilinearMoment (Finset.univ.sigma V) (Finset.univ.sigma V)
        (fun jk => c jk.1 jk.2*fordAdditiveCharacter (η*t jk.1 jk.2))
        (fun jk => c jk.1 jk.2*fordAdditiveCharacter (η*t jk.1 jk.2))
        (fun jk => Real.sqrt (v jk.1 jk.2)-b)
        (fun jk => Real.sqrt (v jk.1 jk.2)-b) (10*R) 0 0 := by
    apply integral_nonneg
    intro η
    apply mul_nonneg (by positivity)
    unfold parabolaBoxBilinearMoment
    exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _)
      (pow_nonneg (norm_nonneg _) 4))
  have hprod := mul_le_mul hS hV hnonnegV (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ E*(6*(b-a)^4)⁻¹ by positivity)
  have he : ((2:ℝ)^((ε/2)*n))^2 = (2:ℝ)^(ε*n) := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ _ := hmain
    _ ≤ _ := by simpa only [s,t,mul_assoc] using hm
    _ = _ := by
      have he' : (2:ℝ)^((ε/2)*n)*(2:ℝ)^((ε/2)*n) = (2:ℝ)^(ε*n) := by
        rw [←pow_two,he]
      calc
        _ = E*D^2*((2:ℝ)^((ε/2)*n)*(2:ℝ)^((ε/2)*n))*(6*(b-a)^4)⁻¹*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (S j) (z j) (fun i => Real.sqrt (w j i)-a))^2)^3*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (V j) (c j) (fun k => Real.sqrt (v j k)-b))^2)^3 := by ring
        _ = _ := by rw [he']

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainCubicQuartic_inverse_moment :
    ∃ C > (0:ℝ), ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s θ : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter
              (θ i+a*(s i)^3+b*(s i)^4+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro a ha b hb ι S z s θ hs
  have hna : -a ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hnb : -b ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hb.2],by linarith [hb.1]⟩
  have hm := h (-a) hna (-b) hnb S
    (fun i => z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4)) s hs
  have hleft :
      (∑ i ∈ S, (z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4))*
        fordAdditiveCharacter (-a*(s i)^3+-b*(s i)^4)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter (θ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  have hright (ξ : ℝ) :
      (∑ i ∈ S, (z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4))*
        fordAdditiveCharacter (ξ*s i)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        (θ i+a*(s i)^3+b*(s i)^4+ξ*s i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
  simpa only [hleft,hright] using hm

private def bourgainCurveCellFrame (a c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,-2*a,3*c^2,8*c^3;
     0,1,-3*c,-6*c^2;
     0,0,1,0;
     0,0,0,1]

private theorem bourgainCurveCellFrame_apply (a c : ℝ) (y : Fin 4 → ℝ) :
    (bourgainCurveCellFrame a c).mulVec y =
      ![y 0-2*a*y 1+3*c^2*y 2+8*c^3*y 3,
        y 1-3*c*y 2-6*c^2*y 3,y 2,y 3] := by
  funext i
  fin_cases i <;>
    simp [bourgainCurveCellFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

private theorem bourgainCurveCellFrame_det (a c : ℝ) :
    (bourgainCurveCellFrame a c).det = 1 := by
  unfold bourgainCurveCellFrame
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix]

private theorem bourgainCurveCellFrame_measurePreserving (a c : ℝ) :
    MeasurePreserving ((bourgainCurveCellFrame a c).mulVec)
      (volume : Measure (Fin 4 → ℝ)) volume := by
  have hc : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  refine ⟨hc.measurable,?_⟩
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (show (bourgainCurveCellFrame a c).det ≠ 0 by rw [bourgainCurveCellFrame_det]; norm_num)
  change Measure.map (bourgainCurveCellFrame a c).mulVec volume = _ at hm
  simpa only [bourgainCurveCellFrame_det,inv_one,abs_one,
    ENNReal.ofReal_one,one_smul] using hm

private theorem bourgainCurveCellFrame_phase (a c δ s : ℝ) (y : Fin 4 → ℝ) :
    let x := (bourgainCurveCellFrame a c).mulVec y
    x 0*(c+δ*s)+x 1*(c+δ*s)^2+x 2*(c+δ*s)^3+x 3*(c+δ*s)^4 =
      (c+δ*s-a)*y 0+(c+δ*s-a)^2*y 1+
        ((y 2+4*c*y 3)*δ^3)*s^3+(y 3*δ^4)*s^4+
        (a*y 0-a^2*y 1+c^3*y 2+3*c^4*y 3) := by
  rw [bourgainCurveCellFrame_apply]
  dsimp
  ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

public  theorem norm_bourgain_character_sum_add {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (θ : ι → ℝ) (k : ℝ) :
    ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i+k)‖ =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖ := by
  have he :
      (∑ i ∈ S, z i*fordAdditiveCharacter (θ i+k)) =
        (∑ i ∈ S, z i*fordAdditiveCharacter (θ i))*fordAdditiveCharacter k := by
    rw [Finset.sum_mul]
    simp only [fordAdditiveCharacter_add,mul_assoc]
  rw [he,norm_mul,sargos_character_norm,mul_one]

private theorem exists_bourgainCurveCell_inverse_pointwise :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |c| ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ R → 5*R*δ^3 ≤ 1 →
      ∀ y : Fin 4 → ℝ, |y 2| ≤ R → |y 3| ≤ R →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*y 0+(c+δ*s i-a)^2*y 1)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter
              ((bourgainCurveCellFrame a c).mulVec y 0*(c+δ*s i)+
                (bourgainCurveCellFrame a c).mulVec y 1*(c+δ*s i)^2+
                (bourgainCurveCellFrame a c).mulVec y 2*(c+δ*s i)^3+
                (bourgainCurveCellFrame a c).mulVec y 3*(c+δ*s i)^4+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_inverse_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs a c δ R hc hδ hδ₁ hR hrem y hy₂ hy₃
  have hcoeff := bourgainQuartic_remainder_bounds hc hδ hδ₁ hR hrem
    ![0,0,y 2,y 3] (by
      intro j
      fin_cases j
      · simpa using hR
      · simpa using hR
      · exact hy₂
      · exact hy₃)
  change |(y 2+4*c*y 3)*δ^3| ≤ 1 ∧ |y 3*δ^4| ≤ 1 at hcoeff
  let P := fun i => (c+δ*s i-a)*y 0+(c+δ*s i-a)^2*y 1
  let A := (y 2+4*c*y 3)*δ^3
  let B := y 3*δ^4
  let K := a*y 0-a^2*y 1+c^3*y 2+3*c^4*y 3
  have hm := h A (abs_le.mp hcoeff.1) B (abs_le.mp hcoeff.2) S z s P hs
  have he (ξ : ℝ) :
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((bourgainCurveCellFrame a c).mulVec y 0*(c+δ*s i)+
          (bourgainCurveCellFrame a c).mulVec y 1*(c+δ*s i)^2+
          (bourgainCurveCellFrame a c).mulVec y 2*(c+δ*s i)^3+
          (bourgainCurveCellFrame a c).mulVec y 3*(c+δ*s i)^4+ξ*s i)‖ =
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (P i+A*(s i)^3+B*(s i)^4+ξ*s i)‖ := by
    calc
      _ = ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((P i+A*(s i)^3+B*(s i)^4+ξ*s i)+K)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
        have hp := bourgainCurveCellFrame_phase a c δ (s i) y
        dsimp only at hp
        rw [hp]
        dsimp [P,A,B,K]
        ring
      _ = _ := norm_bourgain_character_sum_add S z _ K
  simpa only [he,P] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainCurveCellFrame_norm_bound {a c R : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 ≤ R)
    (y : Fin 4 → ℝ) (hy₂ : |y 2| ≤ R) (hy₃ : |y 3| ≤ R) :
    ‖(bourgainCurveCellFrame a c).mulVec y‖ ≤ 14*(|y 0|+|y 1|+R) := by
  have hc2 : |c|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  have hc3 : |c|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  have hrow (i : Fin 4) : (∑ j, |bourgainCurveCellFrame a c i j|) ≤ 14 := by
    fin_cases i <;>
      norm_num [bourgainCurveCellFrame,Fin.sum_univ_succ,abs_mul,abs_pow] <;>
      nlinarith [sq_abs c]
  have hy (j : Fin 4) : |y j| ≤ |y 0|+|y 1|+R := by
    fin_cases j
    · change |y 0| ≤ _
      linarith [abs_nonneg (y 1)]
    · change |y 1| ≤ _
      linarith [abs_nonneg (y 0)]
    · change |y 2| ≤ _
      linarith [abs_nonneg (y 0),abs_nonneg (y 1)]
    · change |y 3| ≤ _
      linarith [abs_nonneg (y 0),abs_nonneg (y 1)]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |bourgainCurveCellFrame a c i j*y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |bourgainCurveCellFrame a c i j| * |y j| := by simp only [abs_mul]
    _ ≤ ∑ j, |bourgainCurveCellFrame a c i j| * (|y 0|+|y 1|+R) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _))
    _ = (∑ j, |bourgainCurveCellFrame a c i j|)*(|y 0|+|y 1|+R) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (by positivity)

private theorem bourgainCurveCellFrame_weight_bound {a c R δ : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 < R) (hδ : 0 < δ)
    (y : Fin 4 → ℝ) (hy₂ : |y 2| ≤ R) (hy₃ : |y 3| ≤ R) (ξ : ℝ) :
    parabolaSourceWeight R 0 0 (y 0) (y 1) ≤
      (32:ℝ)^100*(1+|ξ|/(δ*R))^100*
        ((1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖)^100)⁻¹ := by
  let q := ‖(((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)‖
  let L := |ξ|/(δ*R)
  have hq : 0 ≤ q := norm_nonneg _
  have hL : 0 ≤ L := by positivity
  have hy₀ : |y 0| ≤ R*q := by
    have h := Complex.abs_re_le_norm (((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
      abs_div,abs_of_pos hR] at h
    exact (div_le_iff₀ hR).mp h |>.trans_eq (mul_comm _ _)
  have hy₁ : |y 1| ≤ R*q := by
    have h := Complex.abs_im_le_norm (((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,
      abs_div,abs_of_pos hR] at h
    exact (div_le_iff₀ hR).mp h |>.trans_eq (mul_comm _ _)
  have hshift : ‖(![ξ/δ,0,0,0] : Fin 4 → ℝ)‖ ≤ |ξ|/δ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs,abs_of_pos hδ] <;> positivity
  have hf := bourgainCurveCellFrame_norm_bound ha hc hR.le y hy₂ hy₃
  have hn : ‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖ ≤
      28*q+14+L := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hadd := norm_add_le ((bourgainCurveCellFrame a c).mulVec y) ![ξ/δ,0,0,0]
    have hb : ‖(bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]‖ ≤
        R*(28*q+14+L) := by
      have hRL : R*L = |ξ|/δ := by dsimp [L]; field_simp
      nlinarith only [hadd,hf,hshift,hy₀,hy₁,hRL]
    have h := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hR.ne',one_mul] using h
  have hb : 1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖ ≤
      32*(1+q)*(1+L) := by nlinarith [mul_nonneg hq hL]
  have hp := pow_le_pow_left₀ (by positivity) hb 100
  rw [mul_pow,mul_pow] at hp
  simp only [parabolaSourceWeight,sub_zero]
  change 1/(1+q)^100 ≤ (32:ℝ)^100*(1+L)^100*
    ((1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖)^100)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (1+q)^100)).mpr
  calc
    _ ≤ _ := hp
    _ = _ := by ac_rfl

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private def bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*u i+x 1*(u i)^2+x 2*(u i)^3+x 3*(u i)^4)‖^6

private theorem continuous_bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) :
    Continuous (bourgainCurveCellMoment S z u) := by
  unfold bourgainCurveCellMoment fordAdditiveCharacter
  fun_prop

public  theorem integrable_bourgainCurveCellWeight {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹) := by
  have h := integrable_one_add_norm (E:=Fin 4 → ℝ) (μ:=volume) (r:=100) (by norm_num)
  have hi := h.comp_smul (inv_ne_zero hR.ne')
  have he (x : Fin 4 → ℝ) : (1+‖R⁻¹ • x‖)^(-(100:ℝ)) =
      ((1+‖R⁻¹ • x‖)^100)⁻¹ := by
    rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]
  simpa only [he] using hi

private theorem integrable_bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ =>
      ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
  exact (integrable_bourgainCurveCellWeight hR).mul_bdd
    (continuous_bourgainCurveCellMoment S z u).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => bourgain_character_six_bound S z
      (fun i => x 0*u i+x 1*(u i)^2+x 2*(u i)^3+x 3*(u i)^4)))

private theorem bourgainCurveCellFrame_shift_measurePreserving (a c δ ξ : ℝ) :
    MeasurePreserving
      (fun y : Fin 4 → ℝ => (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])
      volume volume :=
  (measurePreserving_add_right volume ![ξ/δ,0,0,0]).comp
    (bourgainCurveCellFrame_measurePreserving a c)

private theorem bourgainCurveCellFrame_shift_integral (a c δ ξ : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ y : Fin 4 → ℝ, f ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])) =
      ∫ x : Fin 4 → ℝ, f x := by
  have hT := bourgainCurveCellFrame_shift_measurePreserving a c δ ξ
  have h := integral_map (μ:=volume) hT.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq] at h
  exact h.symm

private theorem bourgainCurveCellMoment_shift {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (c ξ : ℝ) {δ : ℝ} (hδ : δ ≠ 0)
    (x : Fin 4 → ℝ) :
    bourgainCurveCellMoment S z (fun i => c+δ*s i) (x+![ξ/δ,0,0,0]) =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+δ*s i)+x 1*(c+δ*s i)^2+x 2*(c+δ*s i)^3+
          x 3*(c+δ*s i)^4+ξ*s i)‖^6 := by
  unfold bourgainCurveCellMoment
  have he :
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((x+![ξ/δ,0,0,0]) 0*(c+δ*s i)+(x+![ξ/δ,0,0,0]) 1*(c+δ*s i)^2+
          (x+![ξ/δ,0,0,0]) 2*(c+δ*s i)^3+(x+![ξ/δ,0,0,0]) 3*(c+δ*s i)^4)‖ =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((x 0*(c+δ*s i)+x 1*(c+δ*s i)^2+x 2*(c+δ*s i)^3+
          x 3*(c+δ*s i)^4+ξ*s i)+ξ*c/δ)‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only [Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      add_zero]
    field_simp
    ring
  rw [he,norm_bourgain_character_sum_add]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private def bourgainCurveCellBaseWeight (R : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  parabolaSourceWeight R 0 0 (y 0) (y 1)*
    (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3)

private theorem bourgainCurveCellBaseWeight_nonneg (R : ℝ) (y : Fin 4 → ℝ) :
    0 ≤ bourgainCurveCellBaseWeight R y :=
  mul_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

private theorem integrable_bourgainCurveCellBaseWeight {R : ℝ} (hR : 0 < R) :
    Integrable (bourgainCurveCellBaseWeight R) := by
  let B := Icc (-R) R ×ˢ Icc (-R) R
  have hi : Integrable (B.indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
    (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  have h := bourgainFourCoordinates_measurePreserving.integrable_comp_of_integrable
    ((integrable_parabolaSourceWeight hR 0 0).mul_prod hi)
  convert h using 1
  rfl

private theorem bourgainCurveCell_transverse_mass {R : ℝ} (hR : 0 ≤ R) :
    (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
      (fun _ : ℝ × ℝ => (1:ℝ)) q) = 4*R^2 := by
  rw [integral_indicator (measurableSet_Icc.prod measurableSet_Icc),integral_const,
    smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
  change (volume.prod volume).real (Icc (-R) R ×ˢ Icc (-R) R) = _
  rw [measureReal_prod_prod,Real.volume_real_Icc_of_le (by linarith),
    sub_neg_eq_add]
  ring

private theorem bourgainCurveCell_inner_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) {a c R δ : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 < R) (hδ : 0 < δ) (ξ : ℝ) :
    (∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
      bourgainCurveCellMoment S z u
        ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])) ≤
      (32:ℝ)^100*(1+|ξ|/(δ*R))^100*
        (∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
  let T := fun y : Fin 4 → ℝ => (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let K := (32:ℝ)^100*(1+|ξ|/(δ*R))^100
  have hcF : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous T := hcF.add continuous_const
  have hi₁ : Integrable (fun y => bourgainCurveCellBaseWeight R y*
      bourgainCurveCellMoment S z u (T y)) :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      ((continuous_bourgainCurveCellMoment S z u).comp hcT).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => bourgain_character_six_bound S z
        (fun i => T y 0*u i+T y 1*(u i)^2+T y 2*(u i)^3+T y 3*(u i)^4)))
  have hi₂ : Integrable (fun y => ((1+‖R⁻¹ • T y‖)^100)⁻¹*
      bourgainCurveCellMoment S z u (T y)) :=
    (bourgainCurveCellFrame_shift_measurePreserving a c δ ξ).integrable_comp_of_integrable
      (integrable_bourgainCurveCellMoment S z u hR)
  have hp (y : Fin 4 → ℝ) :
      bourgainCurveCellBaseWeight R y ≤ K*((1+‖R⁻¹ • T y‖)^100)⁻¹ := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · simp only [bourgainCurveCellBaseWeight,Set.indicator_of_mem hy,mul_one]
      exact bourgainCurveCellFrame_weight_bound ha hc hR hδ y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2) ξ
    · simp only [bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,mul_zero]
      dsimp [K]
      positivity
  have hm := integral_mono hi₁ (hi₂.const_mul K) (fun y => by
    have h := mul_le_mul_of_nonneg_right (hp y)
      (show 0 ≤ bourgainCurveCellMoment S z u (T y) by unfold bourgainCurveCellMoment; positivity)
    simpa only [mul_assoc] using h)
  rw [integral_const_mul] at hm
  have hf : StronglyMeasurable (fun x : Fin 4 → ℝ =>
      ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
    have hwc : Continuous (fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · intro x
        positivity
    exact (hwc.mul (continuous_bourgainCurveCellMoment S z u)).stronglyMeasurable
  have he := bourgainCurveCellFrame_shift_integral a c δ ξ _ hf
  change (∫ y : Fin 4 → ℝ, ((1+‖R⁻¹ • T y‖)^100)⁻¹*
    bourgainCurveCellMoment S z u (T y)) = _ at he
  rw [he] at hm
  exact hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
public  theorem bourgainSourcePermutation_norm (x : Fin 4 → ℝ) :
    ‖bourgainSourcePermutation x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    fin_cases i <;>
      first | exact norm_le_pi_norm x 3 | exact norm_le_pi_norm x 0 |
        exact norm_le_pi_norm x 2 | exact norm_le_pi_norm x 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (bourgainSourcePermutation x))).mpr
    intro i
    fin_cases i <;>
      first | exact norm_le_pi_norm (bourgainSourcePermutation x) 1 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 3 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 2 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 0

private theorem bourgain_modulation_envelope_general {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    ((1+|ξ|)^102)⁻¹*(1+|ξ|/L)^100 ≤
      (1+L⁻¹)^100*(1+ξ^2)⁻¹ := by
  have hbase : 1+|ξ|/L ≤ (1+L⁻¹)*(1+|ξ|) := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hL,abs_nonneg ξ]
  have hp := pow_le_pow_left₀ (by positivity) hbase 100
  rw [mul_pow] at hp
  have henv := bourgain_modulation_envelope (R:=1) (by norm_num) ξ
  simp only [div_one] at henv
  calc
    _ ≤ ((1+|ξ|)^102)⁻¹*((1+L⁻¹)^100*(1+|ξ|)^100) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (1+L⁻¹)^100*(((1+|ξ|)^102)⁻¹*(1+|ξ|)^100) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left henv (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainQuartic_cell_return_quantitative :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*p.1+(c+δ*s i-a)^2*p.2)‖^6) ≤
        C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          bourgainCurveCellMoment S z (fun i => c+δ*s i) x) := by
  obtain ⟨E,hE,hInv⟩ := exists_bourgainCurveCell_inverse_pointwise.{u}
  refine ⟨E*(32:ℝ)^100*Real.pi/4,by positivity,?_⟩
  intro ι S z s hs a c δ R ha hc hδ hδ₁ hR hrem
  let u := fun i => c+δ*s i
  let T := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let P := fun p : ℝ × ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    ((u i-a)*p.1+(u i-a)^2*p.2)‖^6
  let F := fun y : Fin 4 → ℝ => bourgainCurveCellBaseWeight R y*P (y 0,y 1)
  let H := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    W ξ*bourgainCurveCellBaseWeight R y*bourgainCurveCellMoment S z u (T ξ y)
  let J := ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x
  let L := (1+(δ*R)⁻¹)^100
  have hJ : 0 ≤ J := integral_nonneg (fun x => by
    apply mul_nonneg (by positivity)
    unfold bourgainCurveCellMoment
    positivity)
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => (u i-a)*p.1+(u i-a)^2*p.2)
  have hiF : Integrable F :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      (hPc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hPb (y 0,y 1)))
  have hcFrame : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous (fun q : ℝ × (Fin 4 → ℝ) => T q.1 q.2) := by
    exact (hcFrame.comp continuous_snd).add (by dsimp [T]; fun_prop)
  have hcM : Continuous (fun q : ℝ × (Fin 4 → ℝ) =>
      bourgainCurveCellMoment S z u (T q.1 q.2)) :=
    (continuous_bourgainCurveCellMoment S z u).comp hcT
  have hiH : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hp := bourgainRemainderEnvelope_integrable.mul_prod
      (integrable_bourgainCurveCellBaseWeight hR)
    exact hp.mul_bdd hcM.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => bourgain_character_six_bound S z
        (fun i => T q.1 q.2 0*u i+T q.1 q.2 1*(u i)^2+
          T q.1 q.2 2*(u i)^3+T q.1 q.2 3*(u i)^4)))
  have hp (y : Fin 4 → ℝ) : F y ≤ E*(∫ ξ : ℝ, H ξ y) := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · have hm := hInv S z s hs a c δ R hc hδ.le hδ₁ hR.le hrem y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2)
      have he (ξ : ℝ) := bourgainCurveCellMoment_shift S z s c ξ hδ.ne'
        ((bourgainCurveCellFrame a c).mulVec y)
      have hmi : P (y 0,y 1) ≤ E*(∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        simpa only [P,W,u,T,he] using hm
      have hm' := mul_le_mul_of_nonneg_left hmi (bourgainCurveCellBaseWeight_nonneg R y)
      have heH : (∫ ξ : ℝ, H ξ y) = bourgainCurveCellBaseWeight R y*
          (∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp [H]
        ring
      rw [heH]
      simpa only [F,mul_left_comm] using hm'
    · simp only [F,H,bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,
        mul_zero,zero_mul,integral_zero,le_refl]
  have hmain := bourgain_kernel_setIntegral_bound
    (α:=Fin 4 → ℝ) (β:=ℝ) (μ:=volume) (ν:=volume)
    (B:=Set.univ) (C:=E) (f:=F) (H:=H)
    MeasurableSet.univ hiF.integrableOn
    (by simpa only [Measure.restrict_univ] using hiH) (fun y _ => hp y)
  simp only [setIntegral_univ] at hmain

  have hinner (ξ : ℝ) : (∫ y : Fin 4 → ℝ, H ξ y) ≤
      (32:ℝ)^100*J*L*(1+ξ^2)⁻¹ := by
    have hb := bourgainCurveCell_inner_bound S z u ha hc hR hδ ξ
    have heH : (∫ y : Fin 4 → ℝ, H ξ y) =
        W ξ*(∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
          bourgainCurveCellMoment S z u (T ξ y)) := by
      simp only [H,mul_assoc,integral_const_mul]
    rw [heH]
    calc
      _ ≤ W ξ*((32:ℝ)^100*(1+|ξ|/(δ*R))^100*J) :=
        mul_le_mul_of_nonneg_left hb (by dsimp [W]; positivity)
      _ = (32:ℝ)^100*J*(W ξ*(1+|ξ|/(δ*R))^100) := by ring
      _ ≤ (32:ℝ)^100*J*(L*(1+ξ^2)⁻¹) :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope_general (mul_pos hδ hR) ξ)
          (mul_nonneg (by positivity) hJ)
      _ = _ := by ring
  have hiOuter : Integrable (fun ξ : ℝ => ∫ y : Fin 4 → ℝ, H ξ y) :=
    hiH.integral_prod_left
  have hout := integral_mono hiOuter
    (integrable_inv_one_add_sq.const_mul ((32:ℝ)^100*J*L)) hinner
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hout
  have hleft : (∫ y : Fin 4 → ℝ, F y) =
      4*R^2*(∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p) := by
    calc
      _ = ∫ y : Fin 4 → ℝ,
          (parabolaSourceWeight R 0 0 (y 0) (y 1)*P (y 0,y 1))*
            (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3) := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F,bourgainCurveCellBaseWeight]
        ring
      _ = (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*
          (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
            (fun _ : ℝ × ℝ => (1:ℝ)) q) :=
        bourgainFourCoordinates_integral_product
          (fun p : ℝ × ℝ => parabolaSourceWeight R 0 0 p.1 p.2*P p)
          ((Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)))
      _ = _ := by rw [bourgainCurveCell_transverse_mass hR.le]; ring
  rw [hleft] at hmain
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left hout hE.le)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  change (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*R^2 ≤
    (E*(32:ℝ)^100*Real.pi/4)*L*J
  nlinarith only [hfinal]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainSourceCurve_cell_return_quantitative :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ),
      (∀ i ∈ S, 0 ≤ w i) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 →
      (∀ i ∈ S, |Real.sqrt (w i)-c| ≤ δ) →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((Real.sqrt (w i)-a)*p.1+(Real.sqrt (w i)-a)^2*p.2)‖^6) ≤
        C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainQuartic_cell_return_quantitative.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z w hw a c δ R ha hc hδ hδ₁ hR hrem hwindow
  let s := fun i => (Real.sqrt (w i)-c)/δ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    have hh := abs_le.mp (hwindow i hi)
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith [hh.1]
    · apply (div_le_iff₀ hδ).mpr
      linarith [hh.2]
  have hbase (i : ι) : c+δ*s i = Real.sqrt (w i) := by
    dsimp [s]
    field_simp
    ring
  have hmain := h S z s hs a c δ R ha hc hδ hδ₁ hR hrem
  simp_rw [hbase] at hmain
  let f := fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*
    bourgainCurveCellMoment S z (fun i => Real.sqrt (w i)) x
  have he : (∫ x : Fin 4 → ℝ, f x) =
      ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6 := by
    calc
      _ = ∫ x : Fin 4 → ℝ, f (bourgainSourcePermutation x) :=
        (bourgainSourcePermutation_measurePreserving.integral_comp
          bourgainSourcePermutation.measurableEmbedding f).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [f]
        rw [norm_smul,bourgainSourcePermutation_norm,←norm_smul]
        apply congrArg (fun v : ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*v)
        unfold bourgainCurveCellMoment
        apply congrArg (fun v : ℂ => ‖v‖^6)
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
        simpa only [bourgainSourcePermutation_apply,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val] using
          (bourgain_source_quartic_phase (hw i hi) x).symm
  change _ ≤ C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, f x) at hmain
  rw [he] at hmain
  exact hmain



end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in

theorem exists_bourgainSourceCurve_local_cell_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (a b σ R : ℝ),
      0 ≤ a → a+σ ≤ 1 → 0 ≤ b → b+σ ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 < R → 5*R*σ^3 ≤ 1 →
      5*(10*R)*(σ/(2:ℝ)^n)^3 ≤ 1 → 1 ≤ (σ/(2:ℝ)^n)*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
              x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
          ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
            (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
              x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
          C*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*
            (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
              ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
                (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+
                  x 3*Real.sqrt (w j i))‖^6)*
            (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
              ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
                (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+
                  x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨D,hD,hSource⟩ := exists_bourgainSourceCurve_parabolic_cell_bound.{u} hε
  obtain ⟨C,hC,hReturn⟩ := exists_bourgainSourceCurve_cell_return_quantitative.{u}
  let E := C * (2:ℝ)^100
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨D*E^2,by positivity,?_⟩
  intro n a b σ R ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth
    ι τ S V z c w v hw hv hwgrid hvgrid
  let δ := σ/(2:ℝ)^n
  let W := fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2
  let J {κ : Type u} (K : Finset κ) (q : κ → ℂ) (f : κ → ℝ) :=
    ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
      ‖∑ i ∈ K, q i*fordAdditiveCharacter
        (x 0*f i+x 1*(f i)^2+x 2*(f i)^((3:ℝ)/2)+x 3*Real.sqrt (f i))‖^6
  have hδ : 0 < δ := div_pos hσ (by positivity)
  have hδσ : δ ≤ σ := div_le_self hσ.le (one_le_pow₀ (by norm_num))
  have hδ₁ : δ ≤ 1 := hδσ.trans hσ₁
  have hσR : 1 ≤ σ*(10*R) :=
    hδR.trans (mul_le_mul_of_nonneg_right hδσ (by positivity))
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hbabs : |b| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hmain := hSource n a b σ R haabs hbabs hab hσ hσ₁ hR.le hrem hσR hwidth
    ι τ S V z c w v hw hv hwgrid hvgrid
  have hQ (κ : Type u) (K : Fin (2^n) → Finset κ)
      (q : Fin (2^n) → κ → ℂ) (f : Fin (2^n) → κ → ℝ)
      (d : ℝ) (hd : 0 ≤ d) (hdσ : d+σ ≤ 1)
      (hf : ∀ j, ∀ i ∈ K j, 0 ≤ f j i)
      (hgrid : ∀ j, ∀ i ∈ K j, Real.sqrt (f j i) ∈ Icc
        (d+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (d+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) :
      (∑ j, (parabolaWeightedSixNorm W (K j) (q j)
        (fun i => Real.sqrt (f j i)-d))^2)^3 ≤
        ((2:ℝ)^n)^2*(E/(10*R)^2)*(∑ j, J (K j) (q j) (f j)) := by
    have hdabs : |d| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hcell (j : Fin (2^n)) :
        (parabolaWeightedSixNorm W (K j) (q j)
          (fun i => Real.sqrt (f j i)-d))^6 ≤ E/(10*R)^2*J (K j) (q j) (f j) := by
      let e := d+σ*((j:ℕ)/((2^n:ℕ):ℝ))
      have hj : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ) := by positivity
      have hj₁ : ((j:ℕ):ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.le_of_lt j.isLt
      have he₀ : 0 ≤ e := add_nonneg hd (mul_nonneg hσ.le hj)
      have he₁ : e ≤ 1 := by
        have hh := mul_le_mul_of_nonneg_left hj₁ hσ.le
        dsimp [e]
        linarith
      have heabs : |e| ≤ 1 := abs_le.mpr ⟨by linarith,he₁⟩
      have heupper : d+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)) = e+δ := by
        dsimp [e,δ]
        push_cast
        ring
      have hwindow : ∀ i ∈ K j, |Real.sqrt (f j i)-e| ≤ δ := by
        intro i hi
        have hl := (hgrid j i hi).1
        have hh := (hgrid j i hi).2
        rw [heupper] at hh
        change e ≤ Real.sqrt (f j i) at hl
        rw [abs_of_nonneg (sub_nonneg.mpr hl)]
        linarith
      have hr := hReturn (K j) (q j) (f j) (hf j) d e δ (10*R) hdabs heabs
        hδ hδ₁ (by positivity) hfine hwindow
      have hloss : (1+(δ*(10*R))⁻¹)^100 ≤ (2:ℝ)^100 :=
        pow_le_pow_left₀ (by positivity)
          (by linarith [inv_le_one_of_one_le₀ hδR]) _
      have hr' : C*(1+(δ*(10*R))⁻¹)^100/(10*R)^2*J (K j) (q j) (f j) ≤
          E/(10*R)^2*J (K j) (q j) (f j) := by
        dsimp only [E, J]
        gcongr <;> exact integral_nonneg (fun _ => by positivity)
      have hn := parabolaWeightedSixNorm_pow_six W
        (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
        (integrable_parabolaSourceWeight (by positivity : 0 < 10*R) 0 0)
        (K j) (q j) (fun i => Real.sqrt (f j i)-d)
      have hepow (x : ℝ) : x^2*x^4=x^6 := by ring
      rw [hn]
      simpa only [parabolaWeightedBilinearMoment,sargosPlanarSum,mul_assoc,hepow,W,J] using hr.trans hr'
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
      (f:=fun j => (parabolaWeightedSixNorm W (K j) (q j)
        (fun i => Real.sqrt (f j i)-d))^2) (fun _ _ => sq_nonneg _) 2
    norm_num only [show (2+1:ℕ)=3 by omega,←pow_mul,
      show (2*3:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin,
      Nat.cast_pow,Nat.cast_ofNat] at hh
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcell j)
    rw [←Finset.mul_sum] at hsum
    calc
      _ ≤ ((2:ℝ)^n)^2*∑ j, (parabolaWeightedSixNorm W (K j) (q j)
          (fun i => Real.sqrt (f j i)-d))^6 := by
        simpa only [pow_mul] using hh
      _ ≤ ((2:ℝ)^n)^2*(E/(10*R)^2*(∑ j, J (K j) (q j) (f j))) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg ((2:ℝ)^n))
      _ = _ := by ring

  have hS := hQ ι S z w a ha haσ hw hwgrid
  have hV := hQ τ V c v b hb hbσ hv hvgrid
  have hJV : 0 ≤ ∑ j, J (V j) (c j) (v j) := by
    apply Finset.sum_nonneg
    intro j hj
    apply integral_nonneg
    intro x
    positivity
  have hprod := mul_le_mul hS hV (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ D*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹ by positivity)
  have hpow : (2:ℝ)^(ε*n)*((2:ℝ)^n)^4 = (2:ℝ)^((ε+4)*n) := by
    have he : ((2:ℝ)^n)^4 = (2:ℝ)^((4:ℝ)*n) := by
      rw [←Real.rpow_natCast (2:ℝ) n,←Real.rpow_mul_natCast (by norm_num)]
      congr 1
      push_cast
      ring
    rw [he,←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have halg (A B : ℝ) :
      (D*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹)*
        ((((2:ℝ)^n)^2*(E/(10*R)^2)*A)*(((2:ℝ)^n)^2*(E/(10*R)^2)*B)) =
      (D*E^2)*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*A*B := by
    rw [←hpow]
    ring
  calc
    _ ≤ _ := hmain
    _ ≤ _ := by simpa only [W,mul_assoc] using hm
    _ = _ := halg _ _

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  def bourgainRadialWeight (R : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ((1+‖R⁻¹ • x‖)^100)⁻¹

public  theorem bourgainRadialWeight_nonneg (R : ℝ) (x : Fin 4 → ℝ) :
    0 ≤ bourgainRadialWeight R x := by
  unfold bourgainRadialWeight
  positivity

private theorem bourgainRadialWeight_le_one (R : ℝ) (x : Fin 4 → ℝ) :
    bourgainRadialWeight R x ≤ 1 := by
  unfold bourgainRadialWeight
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg (R⁻¹ • x)])

public  theorem continuous_bourgainRadialWeight (R : ℝ) :
    Continuous (bourgainRadialWeight R) := by
  unfold bourgainRadialWeight
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

public  theorem bourgainRadialWeight_distance {R : ℝ} (hR : 0 < R) (x : Fin 4 → ℝ) :
    bourgainRadialWeight R x = ((1+‖x‖/R)^100)⁻¹ := by
  unfold bourgainRadialWeight
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  congr 2
  rw [div_eq_mul_inv,mul_comm]

private theorem integral_bourgainRadialWeight {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x) =
      R^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (Fin 4 → ℝ)) (fun x : Fin 4 → ℝ => ((1+‖x‖)^100)⁻¹) hR
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.cast_ofNat,mul_one,
    bourgainRadialWeight,inv_one,one_smul] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

public  theorem bourgain_inverse_power_ratio {p q L : ℝ}
    (hp : 0 < p) (hq : 0 < q) (h : q ≤ L*p) :
    (p^100)⁻¹ ≤ L^100*(q^100)⁻¹ := by
  rw [←div_eq_mul_inv,le_div_iff₀ (pow_pos hq 100),inv_mul_eq_div,
    div_le_iff₀ (pow_pos hp 100)]
  simpa only [mul_pow] using pow_le_pow_left₀ hq.le h 100

private theorem bourgain_scalar_weight_product {K R X A B : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htriangle : X ≤ A+B) :
    ((1+A/K)^100)⁻¹*((1+B/R)^100)⁻¹ ≤
      (4:ℝ)^100*((1+X/R)^100)⁻¹*
        (((1+A/K)^100)⁻¹+(K/R)^4*((1+B/R)^100)⁻¹) := by
  have hR : 0 < R := hK.trans_le hKR
  have hp : 0 < 1+A/K := by positivity
  have hq : 0 < 1+B/R := by positivity
  have hr : 0 < 1+X/R := by positivity
  have hratio₀ : 0 ≤ K/R := by positivity
  have hratio₁ : K/R ≤ 1 := (div_le_one hR).mpr hKR
  have hW : ((1+B/R)^100)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [div_nonneg hB hR.le]))
  have hfirst (hh : ((1+B/R)^100)⁻¹ ≤ (4:ℝ)^100*((1+X/R)^100)⁻¹) :
      ((1+A/K)^100)⁻¹*((1+B/R)^100)⁻¹ ≤
        (4:ℝ)^100*((1+X/R)^100)⁻¹*
          (((1+A/K)^100)⁻¹+(K/R)^4*((1+B/R)^100)⁻¹) := by
    calc
      _ ≤ ((1+A/K)^100)⁻¹*((4:ℝ)^100*((1+X/R)^100)⁻¹) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (4:ℝ)^100*((1+X/R)^100)⁻¹*((1+A/K)^100)⁻¹ := by ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  by_cases hXB : X ≤ 2*B
  · have hdiv : X/R ≤ 2*(B/R) := by
      calc
        _ ≤ (2*B)/R := div_le_div_of_nonneg_right hXB hR.le
        _ = _ := by ring
    apply hfirst
    have hh := bourgain_inverse_power_ratio hq hr
      (show 1+X/R ≤ 4*(1+B/R) by nlinarith [div_nonneg hB hR.le])
    exact hh
  by_cases hXR : X ≤ R
  · have hxdiv : X/R ≤ 1 := (div_le_one hR).mpr hXR
    have hh := bourgain_inverse_power_ratio (by norm_num : (0:ℝ)<1) hr
      (show 1+X/R ≤ (4:ℝ)*1 by linarith)
    simp only [one_pow,inv_one] at hh
    exact hfirst (hW.trans hh)
  have hXA : X ≤ 2*A := by linarith
  have hden : 1+X/R ≤ (4*K/R)*(1+A/K) := by
    have he : (4*K/R)*(1+A/K) = (4*K+4*A)/R := by field_simp
    rw [he]
    apply (le_div_iff₀ hR).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hR.ne']
    linarith
  have hh := bourgain_inverse_power_ratio hp hr hden
  have hpow : (K/R)^100 ≤ (K/R)^4 := by
    rw [show (100:ℕ)=4+96 by omega,pow_add]
    have h := pow_le_one₀ hratio₀ hratio₁ (n:=96)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (pow_nonneg hratio₀ 4)
  have hlast : ((1+A/K)^100)⁻¹ ≤ (4:ℝ)^100*(K/R)^4*((1+X/R)^100)⁻¹ := by
    calc
      _ ≤ _ := hh
      _ = (4:ℝ)^100*(K/R)^100*((1+X/R)^100)⁻¹ := by
        rw [show 4*K/R=4*(K/R) by ring,mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  calc
    _ ≤ ((4:ℝ)^100*(K/R)^4*((1+X/R)^100)⁻¹)*((1+B/R)^100)⁻¹ :=
      mul_le_mul_of_nonneg_right hlast (by positivity)
    _ = (4:ℝ)^100*((1+X/R)^100)⁻¹*((K/R)^4*((1+B/R)^100)⁻¹) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainRadialWeight_product {K R : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (x y : Fin 4 → ℝ) :
    bourgainRadialWeight K y*bourgainRadialWeight R (x-y) ≤
      (4:ℝ)^100*bourgainRadialWeight R x*
        (bourgainRadialWeight K y+(K/R)^4*bourgainRadialWeight R (x-y)) := by
  have hR : 0 < R := hK.trans_le hKR
  have ht : ‖x‖ ≤ ‖y‖+‖x-y‖ := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa only [bourgainRadialWeight_distance hK,bourgainRadialWeight_distance hR] using
    bourgain_scalar_weight_product hK hKR (norm_nonneg x) (norm_nonneg y)
      (norm_nonneg (x-y)) ht

private theorem exists_bourgainRadialWeight_convolution :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R → ∀ x : Fin 4 → ℝ,
      (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*bourgainRadialWeight R (x-y)) ≤
        C*K^4*bourgainRadialWeight R x := by
  let M := ∫ y : Fin 4 → ℝ, bourgainRadialWeight 1 y
  have hM : 0 ≤ M := integral_nonneg (bourgainRadialWeight_nonneg 1)
  refine ⟨2*(4:ℝ)^100*(M+1),by positivity,?_⟩
  intro K R hK hKR x
  have hR : 0 < R := hK.trans_le hKR
  have hiK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hiR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hiShift := hiR.comp_sub_left x
  have hiProd : Integrable (fun y : Fin 4 → ℝ =>
      bourgainRadialWeight K y*bourgainRadialWeight R (x-y)) :=
    hiK.mul_bdd ((continuous_bourgainRadialWeight R).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (bourgainRadialWeight_nonneg _ _)]
        exact bourgainRadialWeight_le_one _ _))
  have hm := integral_mono hiProd
    ((hiK.add (hiShift.const_mul ((K/R)^4))).const_mul
      ((4:ℝ)^100*bourgainRadialWeight R x))
    (bourgainRadialWeight_product hK hKR x)
  simp only [Pi.add_apply] at hm
  rw [integral_const_mul,integral_add hiK (hiShift.const_mul ((K/R)^4)),
    integral_const_mul,integral_sub_left_eq_self _ volume x,
    integral_bourgainRadialWeight hK.le,integral_bourgainRadialWeight hR.le] at hm
  have he : (K/R)^4*R^4 = K^4 := by
    rw [←mul_pow,div_mul_cancel₀ _ hR.ne']
  calc
    _ ≤ _ := hm
    _ = 2*(4:ℝ)^100*M*K^4*bourgainRadialWeight R x := by
      rw [←mul_assoc ((K/R)^4) (R^4) M,he]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (bourgainRadialWeight_nonneg _ _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK.le 4)
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem exists_bourgainRadialWeight_shift_average :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ (f : (Fin 4 → ℝ) → ℝ) (M : ℝ), Continuous f →
      (∀ x, 0 ≤ f x) → (∀ x, ‖f x‖ ≤ M) →
      (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+z))) ≤
        C*K^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f x) := by
  obtain ⟨C,hC,hconv⟩ := exists_bourgainRadialWeight_convolution
  refine ⟨C,hC,?_⟩
  intro K R hK hKR f M hf hf₀ hfM
  have hR : 0 < R := hK.trans_le hKR
  have hiK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hiR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hiBase : Integrable (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K q.1*bourgainRadialWeight R (q.2-q.1)) (volume.prod volume) := by
    have h := (measurePreserving_prod_neg_add
      (volume : Measure (Fin 4 → ℝ)) (volume : Measure (Fin 4 → ℝ))).integrable_comp_of_integrable
        (hiK.mul_prod hiR)
    simpa only [Function.comp_def,sub_eq_add_neg,add_comm] using h
  have hiH : Integrable (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K q.1*bourgainRadialWeight R (q.2-q.1)*f q.2)
      (volume.prod volume) :=
    hiBase.mul_bdd (hf.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hfM q.2))
  have he (z : Fin 4 → ℝ) :
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+z)) =
        ∫ y : Fin 4 → ℝ, bourgainRadialWeight R (y-z)*f y := by
    calc
      _ = ∫ x : Fin 4 → ℝ, bourgainRadialWeight R ((x+z)-z)*f (x+z) := by
        simp only [add_sub_cancel_right]
      _ = _ := integral_add_right_eq_self
        (fun y : Fin 4 → ℝ => bourgainRadialWeight R (y-z)*f y) z
  have hiLeft : Integrable (fun y : Fin 4 → ℝ =>
      (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*bourgainRadialWeight R (y-z))*f y) := by
    simpa only [integral_mul_const] using hiH.integral_prod_right
  have hiRight := (hiR.mul_bdd hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hfM)).const_mul (C*K^4)
  have hm := integral_mono hiLeft hiRight (fun y => by
    have h := mul_le_mul_of_nonneg_right (hconv K R hK hKR y) (hf₀ y)
    simpa only [mul_assoc] using h)
  rw [integral_const_mul] at hm
  calc
    _ = ∫ z : Fin 4 → ℝ, ∫ y : Fin 4 → ℝ,
        bourgainRadialWeight K z*bourgainRadialWeight R (y-z)*f y := by
      apply integral_congr_ae
      filter_upwards with z
      rw [he,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y : Fin 4 → ℝ, ∫ z : Fin 4 → ℝ,
        bourgainRadialWeight K z*bourgainRadialWeight R (y-z)*f y :=
      integral_integral_swap hiH
    _ = ∫ y : Fin 4 → ℝ,
        (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*bourgainRadialWeight R (y-z))*f y := by
      simp only [integral_mul_const]
    _ ≤ _ := hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainParabola_unit_average :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment S S
          (fun i => z i*fordAdditiveCharacter (ξ*x i))
          (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0) ≤
        C*(∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter (x i*p.1+(x i)^2*p.2)‖^6) := by
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨K*Real.pi,by positivity,?_⟩
  intro ι S z x
  let W := fun p : ℝ × ℝ => parabolaSourceWeight 1 0 0 p.1 p.2
  let J := parabolaSourceBilinearMoment S S z z x x 1 0 0
  have hW₀ : ∀ p, 0 ≤ W p := fun p => parabolaSourceWeight_nonneg _ _ _ _ _
  have hW : Integrable W := integrable_parabolaSourceWeight (by norm_num) 0 0
  have hJ : 0 ≤ J := integral_nonneg (fun p => by
    apply mul_nonneg
    · exact mul_nonneg (hW₀ p) (by positivity)
    · positivity)
  have hm (ξ : ℝ) :
      parabolaSourceBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0 ≤
          (1+|ξ|)^100*J := by
    have hn := pow_le_pow_left₀ (sq_nonneg _)
      (parabola_sourceWeight_modulation S z x (by norm_num : (0:ℝ)<1) 0 0 ξ) 3
    rw [mul_pow,←pow_mul,←pow_mul] at hn
    have hr := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/1)^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hr
    rw [hr] at hn
    norm_num only [show (2*3:ℕ)=6 by omega,div_one] at hn
    rw [parabolaWeightedSixNorm_pow_six W hW₀ hW,
      parabolaWeightedSixNorm_pow_six W hW₀ hW] at hn
    exact hn
  have hp (ξ : ℝ) :
      ((1+|ξ|)^102)⁻¹*parabolaBoxBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0 ≤
          K*J*(1+ξ^2)⁻¹ := by
    have hb := (parabolaBox_le_rapid S S
      (fun i => z i*fordAdditiveCharacter (ξ*x i))
      (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x (by norm_num : (0:ℝ)<1) 0 0).trans
      (parabolaRapid_le_source S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x (by norm_num : (0:ℝ)<1) hcomp 0 0)
    have he := bourgain_modulation_envelope (R:=1) (by norm_num) ξ
    simp only [div_one] at he
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(K*((1+|ξ|)^100*J)) :=
        mul_le_mul_of_nonneg_left
          (hb.trans (mul_le_mul_of_nonneg_left (hm ξ) hK.le)) (by positivity)
      _ = K*J*(((1+|ξ|)^102)⁻¹*(1+|ξ|)^100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hK.le hJ)
  have hi := integrable_bourgain_modulated_box S z x x 1 0 0
  have hh := integral_mono hi (integrable_inv_one_add_sq.const_mul (K*J)) hp
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hh
  have he (r : ℝ) : r^2*r^4=r^6 := by ring
  have hJe : J = ∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2*
      ‖∑ i ∈ S, z i*fordAdditiveCharacter (x i*p.1+(x i)^2*p.2)‖^6 := by
    simp only [J,parabolaSourceBilinearMoment,mul_assoc,he,sargosPlanarSum]
  rw [←hJe]
  exact hh.trans_eq (by ring)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

public  theorem bourgain_cube_mass {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Icc (fun _ : Fin 4 => -R) (fun _ => R)) = (2*R)^4 := by
  change (volume (Icc (fun _ : Fin 4 => -R) (fun _ => R))).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun _ => by linarith)]
  simp only [sub_neg_eq_add,←two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

public  theorem bourgain_finite_box_average {K R : ℝ}
    (hK : 0 ≤ K) (hKR : K ≤ R) (f : (Fin 4 → ℝ) → ℝ)
    (hfc : Continuous f) (hf₀ : ∀ x, 0 ≤ f x) :
    (2*K)^4*(∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f x) ≤
      ∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R),
        ∫ y : Fin 4 → ℝ in Icc (fun _ => -K) (fun _ => K), f (q+y) := by
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  have hpoint (y : Fin 4 → ℝ) (hy : y ∈ B K) :
      (∫ x in B R, f x) ≤ ∫ q in B (2*R), f (q+y) := by
    have hsub : (fun q => q+y) ⁻¹' B R ⊆ B (2*R) := by
      intro q hq
      constructor
      · intro i
        have hl := hq.1 i
        have hu := hy.2 i
        change -R ≤ q i+y i at hl
        change y i ≤ K at hu
        linarith
      · intro i
        have hu := hq.2 i
        have hl := hy.1 i
        change q i+y i ≤ R at hu
        change -K ≤ y i at hl
        linarith
    have hi : IntegrableOn (fun q => f (q+y)) (B (2*R)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hfc.comp (continuous_id.add continuous_const)).continuousOn
    calc
      _ = ∫ q in (fun q => q+y) ⁻¹' B R, f (q+y) :=
        ((measurePreserving_add_right volume y).setIntegral_preimage_emb
          (Homeomorph.addRight y).measurableEmbedding f (B R)).symm
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun q => hf₀ (q+y)))
        (Filter.Eventually.of_forall hsub)
  have hc : Continuous (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2)) :=
    hfc.comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B K))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc) hc.continuousOn
  have hconst : IntegrableOn (fun _y : Fin 4 → ℝ => ∫ x in B R, f x) (B K) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hconst hi.integral_prod_right measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change volume.real (B K)*(∫ x in B R, f x) ≤ _ at hh
  rw [bourgain_cube_mass hK] at hh
  have hswap := integral_integral_swap (f:=fun q y => f (q+y)) hi
  exact hh.trans_eq hswap.symm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  def bourgainSourceSixMoment {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6

private theorem exists_bourgainSourceCurve_small_box :
    ∃ C > (0:ℝ), ∀ {ι τ : Type u} (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
      (∀ i ∈ S, Real.sqrt (w i) ∈ Icc 0 1) →
      (∀ j ∈ V, Real.sqrt (v j) ∈ Icc 0 1) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -(1/10:ℝ)) (fun _ => (1/10:ℝ)),
        bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
        C*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment S z w x)*
          (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment V c v x) := by
  obtain ⟨D,hD,hframe⟩ := exists_bourgainSourceCurve_bilinear_reduction.{u}
  obtain ⟨P,hP,hpar⟩ := exists_bourgainParabola_unit_average.{u}
  obtain ⟨Q,hQ,hret⟩ := exists_bourgainSourceCurve_cell_return_quantitative.{u}
  let A := P*Q*(3:ℝ)^100
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨D*(6:ℝ)⁻¹*A^2,by positivity,?_⟩
  intro ι τ S V z c w v hw hv hs ht
  have hsingle {κ : Type u} (U : Finset κ) (d : κ → ℂ) (u : κ → ℝ)
      (hu : ∀ i ∈ U, 0 ≤ u i) (hr : ∀ i ∈ U, Real.sqrt (u i) ∈ Icc 0 1)
      (a : ℝ) (ha : |a| ≤ 1) :
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment U U
          (fun i => d i*fordAdditiveCharacter (ξ*(Real.sqrt (u i)-a)))
          (fun i => d i*fordAdditiveCharacter (ξ*(Real.sqrt (u i)-a)))
          (fun i => Real.sqrt (u i)-a) (fun i => Real.sqrt (u i)-a) 1 0 0) ≤
        A*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment U d u x) := by
    have hb := hpar U d (fun i => Real.sqrt (u i)-a)
    have hc := hret U d u hu a (1/2) (1/2) 1 ha
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun i hi => abs_le.mpr ⟨by linarith [(hr i hi).1],by linarith [(hr i hi).2]⟩)
    rw [show (1+((1/2:ℝ)*1)⁻¹)=3 by norm_num] at hc
    simp only [one_pow,div_one] at hc
    have hh := hb.trans (mul_le_mul_of_nonneg_left hc hP.le)
    change _ ≤ A*_
    exact hh.trans_eq (by dsimp [A,bourgainRadialWeight,bourgainSourceSixMoment]; ring)
  have hS := hsingle S z w hw hs 0 (by norm_num)
  have hV := hsingle V c v hv ht 1 (by norm_num)
  have hframe' := hframe ι τ S V z c w v hw hv 0 1 1 (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i hi => abs_le.mpr ⟨by linarith [(hs i hi).1],by linarith [(hs i hi).2]⟩)
    (fun j hj => abs_le.mpr ⟨by linarith [(ht j hj).1],by linarith [(ht j hj).2]⟩)
  simp only [div_one,show (10:ℝ)*(1/10)=1 by norm_num,
    sub_zero,one_pow,mul_one] at hframe' hS
  have hV₀ : 0 ≤ ∫ η : ℝ, ((1+|η|)^102)⁻¹*
      parabolaBoxBilinearMoment V V
        (fun j => c j*fordAdditiveCharacter (η*(Real.sqrt (v j)-1)))
        (fun j => c j*fordAdditiveCharacter (η*(Real.sqrt (v j)-1)))
        (fun j => Real.sqrt (v j)-1) (fun j => Real.sqrt (v j)-1) 1 0 0 :=
    integral_nonneg (fun η => mul_nonneg (by positivity)
      (integral_nonneg (fun p => by positivity)))
  have hSJ₀ : 0 ≤ A*(∫ x : Fin 4 → ℝ,
      bourgainRadialWeight 1 x*bourgainSourceSixMoment S z w x) :=
    mul_nonneg hA.le (integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg 1 x) (by
        unfold bourgainSourceSixMoment
        positivity)))
  have hprod := mul_le_mul hS hV hV₀ hSJ₀
  have hmain := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ D*(6:ℝ)⁻¹)
  change _ ≤ _ at hframe'
  calc
    _ ≤ _ := hframe'
    _ = D*(6:ℝ)⁻¹*(_*_) := by ring
    _ ≤ _ := hmain
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgainRadialWeight_translate_large {R : ℝ}
    (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ 2*R) (x : Fin 4 → ℝ) :
    bourgainRadialWeight 1 (x-q) ≤ (2:ℝ)^100*bourgainRadialWeight (20*R) x := by
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h20 : 0 < 20*R := by positivity
  rw [bourgainRadialWeight_distance (by norm_num : (0:ℝ)<1),
    bourgainRadialWeight_distance h20,div_one]
  apply bourgain_inverse_power_ratio (by positivity) (by positivity)
  have hn : ‖x‖ ≤ ‖x-q‖+2*R := by
    calc
      _ = ‖(x-q)+q‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-q‖+‖q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hd : ‖x‖/(20*R) ≤ 1+‖x-q‖ := by
    apply (div_le_iff₀ h20).mpr
    nlinarith [norm_nonneg (x-q),mul_nonneg (sub_nonneg.mpr hR) (norm_nonneg (x-q))]
  linarith [norm_nonneg (x-q)]

private theorem bourgainRadialWeight_translated_integral {R : ℝ}
    (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ 2*R)
    (f : (Fin 4 → ℝ) → ℝ) (M : ℝ) (hc : Continuous f)
    (h₀ : ∀ x, 0 ≤ f x) (hb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*f (x+q)) ≤
      (2:ℝ)^100*(∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*f x) := by
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hw1 : Integrable (bourgainRadialWeight 1) :=
    integrable_bourgainCurveCellWeight (by norm_num)
  have hwR : Integrable (bourgainRadialWeight (20*R)) :=
    integrable_bourgainCurveCellWeight (by positivity)
  have hi1 := (hw1.comp_sub_right q).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hiR := hwR.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hh := integral_mono hi1 (hiR.const_mul ((2:ℝ)^100))
    (fun x => (mul_le_mul_of_nonneg_right
      (bourgainRadialWeight_translate_large hR hq x) (h₀ x)).trans_eq (by ring))
  rw [integral_const_mul] at hh
  calc
    _ = ∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 (x-q)*f x := by
      have he := integral_add_right_eq_self (μ:=volume)
        (fun x : Fin 4 → ℝ => bourgainRadialWeight 1 (x-q)*f x) q
      simpa only [add_sub_cancel_right] using he
    _ ≤ _ := hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem bourgainSourceSixMoment_nonneg {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) :
    0 ≤ bourgainSourceSixMoment S z w x := by
  unfold bourgainSourceSixMoment
  positivity

public  theorem continuous_bourgainSourceSixMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) :
    Continuous (bourgainSourceSixMoment S z w) := by
  unfold bourgainSourceSixMoment fordAdditiveCharacter
  fun_prop

public  theorem bourgainSourceSixMoment_translate {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (q x : Fin 4 → ℝ) :
    bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
      (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))) w x =
        bourgainSourceSixMoment S z w (x+q) := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun v : ℂ => ‖v‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
  simp only [Pi.add_apply]
  ring

private theorem exists_bourgainSourceCurve_box_base :
    ∃ C > (0:ℝ), ∀ R : ℝ, 1 ≤ R →
      ∀ {ι τ : Type u} (S : Finset ι) (V : Finset τ)
        (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
        (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
        (∀ i ∈ S, Real.sqrt (w i) ∈ Icc 0 1) →
        (∀ j ∈ V, Real.sqrt (v j) ∈ Icc 0 1) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
          C*R^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
            bourgainSourceSixMoment S z w x)*
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
              bourgainSourceSixMoment V c v x) := by
  obtain ⟨D,hD,hsmall⟩ := exists_bourgainSourceCurve_small_box.{u}
  refine ⟨D*(2:ℝ)^200*20^4,by positivity,?_⟩
  intro R hR ι τ S V z c w v hw hv hs ht
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  let F := fun x : Fin 4 → ℝ => bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x
  let JS := ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment S z w x
  let JV := ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment V c v x
  have hJS : 0 ≤ JS := integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hJV : 0 ≤ JV := integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hFc : Continuous F :=
    (continuous_bourgainSourceSixMoment S z w).mul (continuous_bourgainSourceSixMoment V c v)
  have hF₀ (x : Fin 4 → ℝ) : 0 ≤ F x :=
    mul_nonneg (bourgainSourceSixMoment_nonneg _ _ _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)
  have havg := bourgain_finite_box_average (K:=1/10) (R:=R)
    (by norm_num) (by linarith) F hFc hF₀
  have hpoint (q : Fin 4 → ℝ) (hq : q ∈ B (2*R)) :
      (∫ y in B (1/10), F (q+y)) ≤ D*(2:ℝ)^200*JS*JV := by
    have hqnorm : ‖q‖ ≤ 2*R := (pi_norm_le_iff_of_nonneg (by linarith)).mpr
      (fun i => by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨hq.1 i,hq.2 i⟩)
    have hmoment {κ : Type u} (U : Finset κ) (d : κ → ℂ) (u : κ → ℝ) :
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*
          bourgainSourceSixMoment U (fun i => d i*fordAdditiveCharacter
            (q 0*u i+q 1*(u i)^2+q 2*(u i)^((3:ℝ)/2)+q 3*Real.sqrt (u i))) u x) ≤
          (2:ℝ)^100*(∫ x : Fin 4 → ℝ,
            bourgainRadialWeight (20*R) x*bourgainSourceSixMoment U d u x) := by
      simp_rw [bourgainSourceSixMoment_translate]
      exact bourgainRadialWeight_translated_integral hR hqnorm
        (bourgainSourceSixMoment U d u) ((∑ i ∈ U, ‖d i‖)^6)
        (continuous_bourgainSourceSixMoment U d u)
        (bourgainSourceSixMoment_nonneg U d u)
        (fun x => bourgain_character_six_bound U d
          (fun i => x 0*u i+x 1*(u i)^2+x 2*(u i)^((3:ℝ)/2)+x 3*Real.sqrt (u i)))
    have hlocal := hsmall S V
      (fun i => z i*fordAdditiveCharacter
        (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i)))
      (fun j => c j*fordAdditiveCharacter
        (q 0*v j+q 1*(v j)^2+q 2*(v j)^((3:ℝ)/2)+q 3*Real.sqrt (v j)))
      w v hw hv hs ht
    have hmS := hmoment S z w
    have hmV := hmoment V c v
    have hleft : (∫ y in B (1/10), F (q+y)) =
        ∫ y in B (1/10),
          bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
            (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))) w y*
          bourgainSourceSixMoment V (fun j => c j*fordAdditiveCharacter
            (q 0*v j+q 1*(v j)^2+q 2*(v j)^((3:ℝ)/2)+q 3*Real.sqrt (v j))) v y := by
      simp only [bourgainSourceSixMoment_translate,F,add_comm]
    rw [hleft]
    refine hlocal.trans ?_
    have hh := mul_le_mul hmS hmV
      (integral_nonneg (fun x => mul_nonneg (bourgainRadialWeight_nonneg _ _)
        (bourgainSourceSixMoment_nonneg _ _ _ _)))
      (mul_nonneg (by positivity) hJS)
    have hh' := mul_le_mul_of_nonneg_left hh hD.le
    change D*_ * _ ≤ D*(2:ℝ)^200*JS*JV
    calc
      _ = D*(_*_) := by ring
      _ ≤ D*(((2:ℝ)^100*JS)*((2:ℝ)^100*JV)) := hh'
      _ = _ := by ring
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => F (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B (1/10)))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (hFc.comp (continuous_fst.add continuous_snd)).continuousOn
  have hconst : IntegrableOn (fun _q : Fin 4 → ℝ => D*(2:ℝ)^200*JS*JV) (B (2*R)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hi.integral_prod_left hconst measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change _ ≤ volume.real (B (2*R))*(D*(2:ℝ)^200*JS*JV) at hh
  rw [bourgain_cube_mass (by linarith : 0 ≤ 2*R)] at hh
  have hfinal := havg.trans hh
  apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<(2*(1/10:ℝ))^4)).mp
  change (2*(1/10:ℝ))^4*(∫ x in B R, F x) ≤
    (2*(1/10:ℝ))^4*((D*(2:ℝ)^200*20^4)*R^4*JS*JV)
  exact hfinal.trans_eq (by ring)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem integrable_bourgainSource_weighted {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ => bourgainRadialWeight R x*bourgainSourceSixMoment S z w x) :=
  (integrable_bourgainCurveCellWeight hR).mul_bdd
    (continuous_bourgainSourceSixMoment S z w).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => bourgain_character_six_bound S z
      (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))))

private theorem bourgainSourceSixMoment_finite_sum {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ)
    (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
      (fun ji => w ji.1 ji.2) x ≤
        (N:ℝ)^5*∑ j, bourgainSourceSixMoment (S j) (z j) (w j) x := by
  let A := fun j : Fin N => ∑ i ∈ S j, z j i*fordAdditiveCharacter
    (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))
  have hn := pow_le_pow_left₀ (norm_nonneg (∑ j, A j)) (norm_sum_le Finset.univ A) 6
  have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => ‖A j‖) (fun _ _ => norm_nonneg _) 5
  simp only [show (5+1:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin] at hh
  simpa only [bourgainSourceSixMoment,Finset.sum_sigma,A] using hn.trans hh

private theorem bourgainSource_weighted_finite_sum {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) x) ≤
      (N:ℝ)^5*∑ j, ∫ x : Fin 4 → ℝ,
        bourgainRadialWeight R x*bourgainSourceSixMoment (S j) (z j) (w j) x := by
  have hi (j : Fin N) := integrable_bourgainSource_weighted (S j) (z j) (w j) hR
  have hsum : Integrable (fun x : Fin 4 → ℝ =>
      ∑ j, bourgainRadialWeight R x*bourgainSourceSixMoment (S j) (z j) (w j) x) :=
    integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hh := integral_mono
    (integrable_bourgainSource_weighted (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) hR)
    (hsum.const_mul ((N:ℝ)^5))
    (fun x => by
      have hp := mul_le_mul_of_nonneg_left (bourgainSourceSixMoment_finite_sum S z w x)
        (bourgainRadialWeight_nonneg R x)
      simpa only [Finset.mul_sum,mul_left_comm] using hp)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hi j)] at hh
  exact hh

theorem exists_bourgainSourceCurve_polynomial_base :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ι τ : Type u)
      (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
      (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
      (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
      (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
      (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc 0 1) →
      (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc 0 1) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -((2:ℝ)^n)^2) (fun _ => ((2:ℝ)^n)^2),
        ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
          (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
            x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
        ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
          (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
            x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
        C*((2:ℝ)^n)^22/(((2:ℝ)^n)^2)^2*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
              (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))‖^6)*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
              (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨C,hC,hbase⟩ := exists_bourgainSourceCurve_box_base.{u}
  refine ⟨C,hC,?_⟩
  intro n ι τ S V z c w v hw hv hs ht
  let N := (2:ℝ)^n
  let R := N^2
  let JS := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) x
  let JV := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) x
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hR : 1 ≤ R := one_le_pow₀ hN
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h20 : 0 < 20*R := by positivity
  have hm := hbase R hR (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun jk => c jk.1 jk.2)
    (fun ji => w ji.1 ji.2) (fun jk => v jk.1 jk.2)
    (fun ji hji => hw ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => hv jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    (fun ji hji => hs ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => ht jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
  have hS := bourgainSource_weighted_finite_sum S z w h20
  have hV := bourgainSource_weighted_finite_sum V c v h20
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hS hV
  have hJS : 0 ≤ JS := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)))
  have hprod := mul_le_mul hS hV
    (integral_nonneg (fun x => mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (bourgainSourceSixMoment_nonneg _ _ _ _)))
    (mul_nonneg (by positivity) hJS)
  have hprod' := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ C*R^4)
  change _ ≤ C*N^22/R^2*JS*JV
  calc
    _ ≤ _ := hm
    _ = C*R^4*(_*_) := by ring
    _ ≤ C*R^4*((N^5*JS)*(N^5*JV)) := hprod'
    _ = C*N^22/R^2*JS*JV := by
      dsimp [R]
      field_simp

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

public  theorem bourgain_radial_bilinear_fubini
    {K R : ℝ} (hK : 0 < K) (f g : (Fin 4 → ℝ) → ℝ) (Mf Mg : ℝ)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfb : ∀ x, ‖f x‖ ≤ Mf) (hgb : ∀ x, ‖g x‖ ≤ Mg) :
    Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
        (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f (q+p.1)*g (q+p.2))) ∧
    ((∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y))) =
      ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
          (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f (q+p.1)*g (q+p.2))) ∧
    IntegrableOn (fun q : Fin 4 → ℝ =>
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y)))
      (Icc (fun _ => -R) (fun _ => R)) := by
  let B := Icc (fun _ : Fin 4 => -R) (fun _ => R)
  let H := fun (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) (q : Fin 4 → ℝ) =>
    bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*(f (q+p.1)*g (q+p.2))
  have hMf : 0 ≤ Mf := (norm_nonneg (f 0)).trans (hfb 0)
  have hw : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hconst : IntegrableOn (fun _q : Fin 4 → ℝ => (1:ℝ)) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hc : Continuous (fun p : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
      f (p.2+p.1.1)*g (p.2+p.1.2)) :=
    (hfc.comp (continuous_snd.add continuous_fst.fst)).mul
      (hgc.comp (continuous_snd.add continuous_fst.snd))
  have hiH : Integrable (Function.uncurry H)
      ((volume.prod volume).prod (volume.restrict B)) := by
    have hwprod := (hw.mul_prod hw).mul_prod hconst
    have hi := hwprod.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul (hfb _) (hgb _) (norm_nonneg _) hMf))
    convert hi using 1
    funext p
    simp only [Function.uncurry,H,mul_one]
  have he (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) :
      (∫ q in B, H p q) =
        bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
          (∫ q in B, f (q+p.1)*g (q+p.2)) := by
    simp only [H,integral_const_mul]
  have heq (q : Fin 4 → ℝ) : (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q) =
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y)) := by
    calc
      _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
          (bourgainRadialWeight K p.1*f (q+p.1))*
            (bourgainRadialWeight K p.2*g (q+p.2)) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [H]
        ring
      _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
        (fun x : Fin 4 → ℝ => bourgainRadialWeight K x*f (q+x))
        (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*g (q+y))
  refine ⟨?_,?_,?_⟩
  · convert hiH.integral_prod_left using 1
    simp only [Function.uncurry,he,B]
  · have hswap := integral_integral_swap (f:=H) hiH
    calc
      _ = ∫ q in B, ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q := by
        simp only [heq,B]
      _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), ∫ q in B, H p q := hswap.symm
      _ = _ := by simp only [he,B]

  · have hiR : Integrable (fun q : Fin 4 → ℝ =>
        ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q) (volume.restrict B) :=
      hiH.integral_prod_right
    simpa only [heq,B,IntegrableOn] using hiR

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem integrable_bourgainRadial_shift_average
    {K R : ℝ} (hK : 0 < K) (hR : 0 < R)
    (f : (Fin 4 → ℝ) → ℝ) (M : ℝ) (hc : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+y))) := by
  have hwK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hwR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hprod := hwK.mul_prod hwR
  have hi := hprod.mul_bdd
    (hc.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hb (p.2+p.1)))
  convert hi.integral_prod_left using 1
  funext y
  simp only [mul_assoc,integral_const_mul,Function.comp_apply,Pi.add_apply]

private theorem integrable_bourgainSource_shift_sum
    {K R : ℝ} (hK : 0 < K) (hR : 0 < R) {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ) :
    Integrable (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*
      (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
        bourgainSourceSixMoment (S j) (z j) (w j) (x+y))) := by
  have hi (j : Fin N) := integrable_bourgainRadial_shift_average hK hR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))
  simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hi j)

private theorem exists_bourgainSource_shift_sum :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ (N : ℕ) {ι : Type u} (S : Fin N → Finset ι)
        (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ),
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
          (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
            bourgainSourceSixMoment (S j) (z j) (w j) (x+y))) ≤
          C*K^4*(∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
            bourgainSourceSixMoment (S j) (z j) (w j) x) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainRadialWeight_shift_average
  refine ⟨C,hC,?_⟩
  intro K R hK hKR N ι S z w
  have hR : 0 < R := hK.trans_le hKR
  have hi (j : Fin N) := integrable_bourgainRadial_shift_average hK hR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply Finset.sum_le_sum
  intro j hj
  exact h K R hK hKR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (bourgainSourceSixMoment_nonneg (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem bourgainSourceSixMoment_norm_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) :
    ‖bourgainSourceSixMoment S z w x‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
  bourgain_character_six_bound S z
    (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))

set_option maxHeartbeats 400000 in
public  theorem exists_bourgainSourceCurve_averaged_local_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (a b σ R K : ℝ),
      0 ≤ a → a+σ ≤ 1 → 0 ≤ b → b+σ ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 < R → 5*R*σ^3 ≤ 1 →
      5*(10*R)*(σ/(2:ℝ)^n)^3 ≤ 1 → 1 ≤ (σ/(2:ℝ)^n)*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 → 0 < K → K ≤ 10*R →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma S)
              (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) (q+y))*
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma V)
              (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2) (q+y))) ≤
          C*K^8*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*
            (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
              bourgainSourceSixMoment (S j) (z j) (w j) x)*
            (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
              bourgainSourceSixMoment (V j) (c j) (v j) x) := by
  obtain ⟨D,hD,hlocal⟩ := exists_bourgainSourceCurve_local_cell_decoupling.{u} hε
  obtain ⟨E,hE,havg⟩ := exists_bourgainSource_shift_sum.{u}
  refine ⟨D*E^2,by positivity,?_⟩
  intro n a b σ R K ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth hK hKR
    ι τ S V z c w v hw hv hs ht
  let F := bourgainSourceSixMoment (Finset.univ.sigma S)
    (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  let G := bourgainSourceSixMoment (Finset.univ.sigma V)
    (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  let JS := fun y : Fin 4 → ℝ => ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) (x+y)
  let JV := fun y : Fin 4 → ℝ => ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) (x+y)
  let AS := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) x
  let AV := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) x
  let A := D*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h10 : 0 < 10*R := by positivity
  have hFub := bourgain_radial_bilinear_fubini (R:=R) hK F G
    ((∑ ji ∈ Finset.univ.sigma S, ‖z ji.1 ji.2‖)^6)
    ((∑ ji ∈ Finset.univ.sigma V, ‖c ji.1 ji.2‖)^6)
    (continuous_bourgainSourceSixMoment (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2))
    (continuous_bourgainSourceSixMoment (Finset.univ.sigma V)
      (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2))
    (bourgainSourceSixMoment_norm_bound (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2))
    (bourgainSourceSixMoment_norm_bound (Finset.univ.sigma V)
      (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2))
  have hp (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) :
      (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        F (q+p.1)*G (q+p.2)) ≤ A*JS p.1*JV p.2 := by
    have hh := hlocal n a b σ R ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth
      ι τ S V
      (fun j i => z j i*fordAdditiveCharacter
        (p.1 0*w j i+p.1 1*(w j i)^2+p.1 2*(w j i)^((3:ℝ)/2)+p.1 3*Real.sqrt (w j i)))
      (fun j i => c j i*fordAdditiveCharacter
        (p.2 0*v j i+p.2 1*(v j i)^2+p.2 2*(v j i)^((3:ℝ)/2)+p.2 3*Real.sqrt (v j i)))
      w v hw hv hs ht
    change (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      bourgainSourceSixMoment (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2*fordAdditiveCharacter
          (p.1 0*w ji.1 ji.2+p.1 1*(w ji.1 ji.2)^2+
            p.1 2*(w ji.1 ji.2)^((3:ℝ)/2)+p.1 3*Real.sqrt (w ji.1 ji.2)))
        (fun ji => w ji.1 ji.2) q*
      bourgainSourceSixMoment (Finset.univ.sigma V)
        (fun ji => c ji.1 ji.2*fordAdditiveCharacter
          (p.2 0*v ji.1 ji.2+p.2 1*(v ji.1 ji.2)^2+
            p.2 2*(v ji.1 ji.2)^((3:ℝ)/2)+p.2 3*Real.sqrt (v ji.1 ji.2)))
        (fun ji => v ji.1 ji.2) q) ≤
      A*(∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
        bourgainSourceSixMoment (S j)
          (fun i => z j i*fordAdditiveCharacter
            (p.1 0*w j i+p.1 1*(w j i)^2+p.1 2*(w j i)^((3:ℝ)/2)+p.1 3*Real.sqrt (w j i))) (w j) x)*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
          bourgainSourceSixMoment (V j)
            (fun i => c j i*fordAdditiveCharacter
              (p.2 0*v j i+p.2 1*(v j i)^2+p.2 2*(v j i)^((3:ℝ)/2)+p.2 3*Real.sqrt (v j i))) (v j) x) at hh
    simpa only [bourgainSourceSixMoment_translate,F,G,JS,JV] using hh
  have hiS := integrable_bourgainSource_shift_sum hK h10 S z w
  have hiV := integrable_bourgainSource_shift_sum hK h10 V c v
  have hiRight : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      A*((bourgainRadialWeight K p.1*JS p.1)*(bourgainRadialWeight K p.2*JV p.2))) :=
    (hiS.mul_prod hiV).const_mul A
  have hout := integral_mono hFub.1 hiRight
    (fun p => by
      have hh := mul_le_mul_of_nonneg_left (hp p)
        (mul_nonneg (bourgainRadialWeight_nonneg K p.1) (bourgainRadialWeight_nonneg K p.2))
      exact hh.trans_eq (by ring))
  have hfactor : (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
      (bourgainRadialWeight K p.1*JS p.1)*(bourgainRadialWeight K p.2*JV p.2)) =
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*JS x)*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*JV y) :=
    integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Fin 4 → ℝ => bourgainRadialWeight K x*JS x)
      (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*JV y)
  rw [integral_const_mul,hfactor] at hout
  have hmS := havg K (10*R) hK hKR (2^n) S z w
  have hmV := havg K (10*R) hK hKR (2^n) V c v
  have hAS : 0 ≤ AS := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg (10*R) x) (bourgainSourceSixMoment_nonneg (S j) (z j) (w j) x)))
  have hJV : 0 ≤ ∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*JV y :=
    integral_nonneg (fun y => mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
        mul_nonneg (bourgainRadialWeight_nonneg (10*R) x) (bourgainSourceSixMoment_nonneg (V j) (c j) (v j) (x+y))))))
  have hprod := mul_le_mul hmS hmV hJV (mul_nonneg (by positivity) hAS)
  have hmain := hout.trans (mul_le_mul_of_nonneg_left hprod hA)
  rw [hFub.2.1]
  change _ ≤ (D*E^2)*K^8*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*AS*AV
  exact hmain.trans_eq (by dsimp [A]; ring)

end TaoTrudgianYang2025

noncomputable section
open Set
namespace TaoTrudgianYang2025

public  theorem bourgain_coarse_center_separation {a b σ ν u v : ℝ}
    (hν : 0 < ν) (hσ : σ ≤ ν/2)
    (hu : u ∈ Icc a (a+σ)) (hv : v ∈ Icc b (b+σ))
    (hsep : ν ≤ |u-v|) :
    ν/2 ≤ |b-a| ∧ a ≠ b ∧ (6*(b-a)^4)⁻¹ ≤ (6*(ν/2)^4)⁻¹ := by
  have hh : |u-v| ≤ |a-b|+σ := by
    apply abs_le.mpr
    constructor
    · linarith [hu.1,hv.2,neg_abs_le (a-b)]
    · linarith [hu.2,hv.1,le_abs_self (a-b)]
  have hd : ν/2 ≤ |b-a| := by
    rw [abs_sub_comm a b] at hh
    linarith
  have hab : a ≠ b := by
    intro he
    rw [he,sub_self,abs_zero] at hd
    linarith
  have hp : (ν/2)^4 ≤ (b-a)^4 := by
    have h := pow_le_pow_left₀ (by positivity) hd 4
    simpa only [show (4:ℕ)=2*2 by omega,pow_mul,sq_abs] using h
  exact ⟨hd,hab,inv_anti₀ (by positivity)
    (mul_le_mul_of_nonneg_left hp (by norm_num))⟩

end TaoTrudgianYang2025

noncomputable section
namespace TaoTrudgianYang2025

public  theorem bourgain_bootstrap_depth {n : ℕ} (hn : 9 ≤ n) :
    let m := (2*n+2)/3+2
    m < n ∧ 2*n+6 ≤ 3*m ∧ n ≤ 2*m := by
  dsimp
  omega

public  theorem bourgain_bootstrap_scale_conditions {n m : ℕ}
    (hm : m ≤ n) (hlarge : 2*n+6 ≤ 3*m) (hn : 7 ≤ n) :
    let N := (2:ℝ)^n
    let M := (2:ℝ)^m
    let σ := 1/M
    let δ := σ/(2:ℝ)^(n-m)
    0 < σ ∧ σ ≤ 1 ∧ δ=1/N ∧
      5*(2*N^2)*σ^3 ≤ 1 ∧
      5*(10*(2*N^2))*δ^3 ≤ 1 ∧
      1 ≤ δ*(10*(2*N^2)) ∧
      3/(100*(10*(2*N^2))) ≤ δ^2 ∧
      0 < 20*M^2 ∧ 20*M^2 ≤ 10*(2*N^2) := by
  let N := (2:ℝ)^n
  let M := (2:ℝ)^m
  have hN : 0 < N := by dsimp [N]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hN₁ : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hM₁ : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMN : M ≤ N := pow_le_pow_right₀ (by norm_num) hm
  have hN128 : (128:ℝ) ≤ N := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num only [show (2:ℝ)^7=128 by norm_num] at h
    exact h
  have hpow : N^2*64 ≤ M^3 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      (by omega : n*2+6 ≤ m*3)
    rw [pow_add,pow_mul,pow_mul] at h
    norm_num only [show (2:ℝ)^6=64 by norm_num] at h
    exact h
  have hδ : (1/M)/(2:ℝ)^(n-m)=1/N := by
    dsimp [M,N]
    rw [pow_sub₀ (2:ℝ) (by norm_num) hm]
    field_simp
  change 0 < 1/M ∧ 1/M ≤ 1 ∧ (1/M)/(2:ℝ)^(n-m)=1/N ∧ _
  refine ⟨by positivity,(div_le_one hM).mpr hM₁,hδ,?_,?_,?_,?_,by positivity,?_⟩
  · have he : 5*(2*N^2)*(1/M)^3 = 10*N^2/M^3 := by ring
    rw [he]
    apply (div_le_one (pow_pos hM 3)).mpr
    nlinarith [sq_nonneg N]
  · rw [hδ]
    have he : 5*(10*(2*N^2))*(1/N)^3 = 100/N := by field_simp; ring
    rw [he]
    exact (div_le_one hN).mpr (by linarith)
  · rw [hδ]
    have he : (1/N)*(10*(2*N^2)) = 20*N := by field_simp; ring
    rw [he]
    linarith
  · rw [hδ,div_pow,one_pow]
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hN)).mpr
    nlinarith [sq_nonneg N]
  · have hp := pow_le_pow_left₀ hM.le hMN 2
    nlinarith

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  def BourgainSourceGridBound (N : ℕ) (ν D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (ι τ : Type u)
    (S : Fin N → Finset ι) (V : Fin N → Finset τ)
    (z : Fin N → ι → ℂ) (c : Fin N → τ → ℂ)
    (w : Fin N → ι → ℝ) (v : Fin N → τ → ℝ),
    (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
    (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc ((j:ℕ)/(N:ℝ)) (((j:ℕ)+1)/(N:ℝ))) →
    (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc ((j:ℕ)/(N:ℝ)) (((j:ℕ)+1)/(N:ℝ))) →
    (∀ j k, ∀ i ∈ S j, ∀ l ∈ V k, ν ≤ |Real.sqrt (w j i)-Real.sqrt (v k l)|) →
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -(N:ℝ)^2) (fun _ => (N:ℝ)^2),
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) x*
      bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
        (fun ji => v ji.1 ji.2) x) ≤
      D/((N:ℝ)^2)^2*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
          bourgainSourceSixMoment (S j) (z j) (w j) x)*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
          bourgainSourceSixMoment (V j) (c j) (v j) x)

public  theorem bourgainSourceGridBound_mono {N : ℕ} {ν D E : ℝ}
    (hD : BourgainSourceGridBound.{u} N ν D) (hDE : D ≤ E) :
    BourgainSourceGridBound.{u} N ν E := by
  refine ⟨hD.1.trans hDE,?_⟩
  intro ι τ S V z c w v hw hv hs ht hsep
  have hm := hD.2 ι τ S V z c w v hw hv hs ht hsep
  have hS : 0 ≤ ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
      bourgainSourceSixMoment (S j) (z j) (w j) x :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg (S j) (z j) (w j) x)))
  have hV : 0 ≤ ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
      bourgainSourceSixMoment (V j) (c j) (v j) x :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg (V j) (c j) (v j) x)))
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDE (by positivity)) hS) hV)

public  theorem exists_bourgainSourceGridBound_polynomial :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ν : ℝ),
      BourgainSourceGridBound.{u} (2^n) ν (C*((2:ℝ)^n)^22) := by
  obtain ⟨C,hC,hbase⟩ := exists_bourgainSourceCurve_polynomial_base.{u}
  refine ⟨C,hC,?_⟩
  intro n ν
  refine ⟨by positivity,?_⟩
  intro ι τ S V z c w v hw hv hs ht _hsep
  have hunit {κ : Type u} (U : Fin (2^n) → Finset κ) (u : Fin (2^n) → κ → ℝ)
      (hu : ∀ j, ∀ i ∈ U j, Real.sqrt (u j i) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      ∀ j, ∀ i ∈ U j, Real.sqrt (u j i) ∈ Icc 0 1 := by
    intro j i hi
    refine ⟨(by positivity : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ)).trans (hu j i hi).1,?_⟩
    apply (hu j i hi).2.trans
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hm := hbase n ι τ S V z c w v hw hv (hunit S w hs) (hunit V v ht)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,bourgainRadialWeight,bourgainSourceSixMoment] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

public  theorem bourgainSource_grid_coarse_interval {k l : ℕ}
  (hk : 0 < k) (hl : 0 < l) {κ : Type u} (A : Fin (k*l) → Finset κ) (f : Fin (k*l) → κ → ℝ)
    (hgrid : ∀ j, ∀ i ∈ A j, Real.sqrt (f j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ))) :
    ∀ i : Fin k, ∀ ji ∈ Finset.univ.sigma (fun j : Fin l => A (finProdFinEquiv (i,j))),
      Real.sqrt (f (finProdFinEquiv (i,ji.1)) ji.2) ∈ Icc ((i:ℕ)/(k:ℝ)) (((i:ℕ)+1)/(k:ℝ)) := by
  intro i ji hji
  have hf := hgrid (finProdFinEquiv (i,ji.1)) ji.2 (Finset.mem_sigma.mp hji).2
  have hcell := LogarithmicSixth.logCurve_finGrid_cell hk hl i ji.1
  simp only [Nat.cast_mul] at hf
  change Real.sqrt (f (finProdFinEquiv (i,ji.1)) ji.2) ∈ Icc
    (((finProdFinEquiv (i,ji.1) : Fin (k*l)):ℕ)/(k*l:ℝ))
    ((((finProdFinEquiv (i,ji.1) : Fin (k*l)):ℕ)+1)/(k*l:ℝ)) at hf
  rw [hcell.1,hcell.2] at hf
  have hj₀ : (0:ℝ) ≤ (ji.1:ℕ)/(l:ℝ) := by positivity
  have hj₁ : ((ji.1:ℕ)+1)/(l:ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt ji.1.isLt
  refine ⟨(le_add_of_nonneg_right (mul_nonneg (by positivity) hj₀)).trans hf.1,?_⟩
  calc
    _ ≤ (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((ji.1:ℕ)+1)/(l:ℝ)) := hf.2
    _ ≤ (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*1 := add_le_add_right
      (mul_le_mul_of_nonneg_left hj₁ (by positivity)) _
    _ = ((i:ℕ)+1)/(k:ℝ) := by ring

public  theorem bourgainSourceSixMoment_grid_reindex {k l : ℕ} {ι : Type*}
    (S : Fin (k*l) → Finset ι) (z : Fin (k*l) → ι → ℂ) (w : Fin (k*l) → ι → ℝ)
    (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ri => z ri.1 ri.2)
      (fun ri => w ri.1 ri.2) x =
    bourgainSourceSixMoment
      (Finset.univ.sigma (fun i : Fin k => Finset.univ.sigma
        (fun j : Fin l => S (finProdFinEquiv (i,j)))))
      (fun ijv => z (finProdFinEquiv (ijv.1,ijv.2.1)) ijv.2.2)
      (fun ijv => w (finProdFinEquiv (ijv.1,ijv.2.1)) ijv.2.2) x := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun q : ℂ => ‖q‖^6)
  simp only [Finset.sum_sigma]
  exact LogarithmicSixth.logCurve_finGrid_sum (fun r => ∑ i ∈ S r, z r i*fordAdditiveCharacter
    (x 0*w r i+x 1*(w r i)^2+x 2*(w r i)^((3:ℝ)/2)+x 3*Real.sqrt (w r i)))

-- Generated closures: source context is replayed in the next part.
end TaoTrudgianYang2025
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
