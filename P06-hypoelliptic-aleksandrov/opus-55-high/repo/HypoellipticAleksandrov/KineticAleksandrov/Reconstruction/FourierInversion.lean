module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Fourier inversion for finite measures with integrable Fourier transform

Let `μ` be a finite Borel measure on a finite-dimensional real inner product space `V` of
dimension `d`, and write `μ̂(ξ) = ∫ e^{-i⟨ξ,x⟩} dμ(x)`.  If `μ̂` is Lebesgue integrable, then
`μ` has the continuous density
`z ↦ (2π)^{-d} Re ∫ e^{i⟨ξ,z⟩} μ̂(ξ) dξ`, which is nonnegative and bounded by
`(2π)^{-d} ‖μ̂‖₁` (`eq_withDensity_invDensity`, `invDensity_nonneg`, `invDensity_le`).

The proof regularises by a Gaussian.  For `c > 0` the Gaussian-damped inversion integral is the
density `∫ gaussPeak c (z - x) dμ(x)` of `μ` convolved with a Gaussian peak of width `1/c`
(`two_pi_pow_mul_regDensity`).  As `c → ∞` this converges pointwise to the inversion integral
by dominated convergence (`tendsto_regDensity`), and weakly to `μ` against compactly supported
continuous test functions (`tendsto_integral_mul_regDensity`).  Compactly supported test
functions then identify `μ` with the limiting density (Riesz-Markov uniqueness).
-/

@[expose] public section

noncomputable section

open MeasureTheory Complex Filter Topology Module
open scoped RealInnerProductSpace ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

section Peak


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gaussian profile `π^{d/2} e^{-π²‖w‖²}` of integral one. -/
def peakProfile (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w : V) : ℝ :=
  Real.pi ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-Real.pi ^ 2 * ‖w‖ ^ 2)

/-- Gaussian peak kernel `c^d π^{d/2} e^{-π² c² ‖u‖²}`. -/
def gaussPeak (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (c : ℝ) (u : V) : ℝ :=
  c ^ finrank ℝ V * peakProfile V (c • u)

/-- Damping parameter. -/
def dampingParam (c : ℝ) : ℝ := (4 * Real.pi ^ 2 * c ^ 2)⁻¹

/-- The damping parameter is positive for `c > 0`. -/
lemma dampingParam_pos {c : ℝ} (hc : 0 < c) : 0 < dampingParam c := by
  unfold dampingParam
  positivity

/-- Normalising constants: `(2π)^{-n} (π / b_c)^{n/2} = c^n π^{n/2}`. -/
lemma peak_const (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ((2 * Real.pi) ^ n)⁻¹ * (Real.pi / dampingParam c) ^ (n / 2 : ℝ) =
      c ^ n * Real.pi ^ (n / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have h1 : Real.pi / dampingParam c = (2 * Real.pi * c) ^ 2 * Real.pi := by
    unfold dampingParam
    grind
  have h2 : ((2 * Real.pi * c) ^ 2 * Real.pi) ^ (n / 2 : ℝ) =
      (2 * Real.pi * c) ^ n * Real.pi ^ (n / 2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hpi.le, ← Real.rpow_natCast (2 * Real.pi * c) 2,
      ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (2 * Real.pi * c) n]
    ring
  rw [h1, h2]
  field_simp
  ring

/-- The damping parameter tends to zero as `c → ∞`. -/
lemma tendsto_dampingParam : Tendsto dampingParam atTop (𝓝 0) := by
  have h : Tendsto (fun c : ℝ => 4 * Real.pi ^ 2 * c ^ 2) atTop atTop := Tendsto.const_mul_atTop (by positivity) (tendsto_pow_atTop two_ne_zero)
  exact tendsto_inv_atTop_zero.comp h

/-- The Gaussian damping factor has modulus at most one. -/
lemma norm_damp_le_one {V : Type*} [NormedAddCommGroup V] {c : ℝ} (hc : 0 < c) (ξ : V) :
    ‖cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have := dampingParam_pos hc
  simp [← Complex.ofReal_pow]
  positivity

/-- The Gaussian peak kernel is nonnegative. -/
lemma gaussPeak_nonneg {c : ℝ} (hc : 0 ≤ c) (u : V) : 0 ≤ gaussPeak V c u := by
  unfold gaussPeak peakProfile
  positivity

/-- The Gaussian profile is nonnegative. -/
lemma peakProfile_nonneg (w : V) : 0 ≤ peakProfile V w := by
  unfold peakProfile; positivity

/-- The Gaussian peak kernel is bounded by its value at the origin. -/
lemma gaussPeak_le {c : ℝ} (hc : 0 ≤ c) (u : V) :
    gaussPeak V c u ≤ c ^ finrank ℝ V * Real.pi ^ (finrank ℝ V / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have h : Real.exp (-Real.pi ^ 2 * ‖c • u‖ ^ 2) ≤ 1 := by
    simp_all
  calc c ^ finrank ℝ V * (Real.pi ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-Real.pi ^ 2 * ‖c • u‖ ^ 2))
      ≤ c ^ finrank ℝ V * (Real.pi ^ (finrank ℝ V / 2 : ℝ) * 1) := by gcongr
    _ = _ := by ring

/-- The Gaussian peak kernel is continuous. -/
lemma continuous_gaussPeak (c : ℝ) : Continuous (gaussPeak V c) := by
  unfold gaussPeak peakProfile
  fun_prop

end Peak

section Main

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Fourier transform of a finite measure with the convention `e^{-i⟨ξ,x⟩}`. -/
def measureFourier (μ : Measure V) (ξ : V) : ℂ :=
  ∫ x, cexp (-((⟪ξ, x⟫ : ℝ) * I)) ∂μ

/-- The Fourier transform of the damping Gaussian is the Gaussian peak kernel. -/
lemma gaussian_inner_integral {c : ℝ} (hc : 0 < c) (w : V) :
    ∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 + I * ((⟪w, ξ⟫ : ℝ) : ℂ)) =
      (((2 * Real.pi) ^ finrank ℝ V * gaussPeak V c w : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hb : 0 < (((dampingParam c) : ℂ)).re := dampingParam_pos hc
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb I w]
  have h1 : (Real.pi / ((dampingParam c : ℝ))) ^ ((finrank ℝ V : ℂ) / 2) =
      (((Real.pi / dampingParam c) ^ ((finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (div_nonneg hpi.le (dampingParam_pos hc).le)]
    simp
  have h2 : I ^ 2 * (‖w‖) ^ 2 / (4 * ((dampingParam c : ℝ))) =
      ((-Real.pi ^ 2 * ‖c • w‖ ^ 2 : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    unfold dampingParam
    push_cast
    field_simp
    simp
  rw [h1, h2, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  unfold gaussPeak peakProfile
  have hk := peak_const (finrank ℝ V) hc
  have hA : (Real.pi / dampingParam c) ^ ((finrank ℝ V : ℝ) / 2) =
      (2 * Real.pi) ^ finrank ℝ V * (c ^ finrank ℝ V * Real.pi ^ ((finrank ℝ V : ℝ) / 2)) := by
    rw [← hk, mul_inv_cancel_left₀ (by positivity)]
  grind

/-- Fubini: the Gaussian-damped inversion integral is `(2π)^d` times the Gaussian
regularisation `∫ gaussPeak c (z - x) dμ(x)` of `μ`. -/
lemma regularized_eq (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (z : V) :
    ∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ) =
      ((2 * Real.pi) ^ finrank ℝ V : ℝ) * ∫ x, ((gaussPeak V c (z - x) : ℝ) : ℂ) ∂μ := by
  set b : ℂ := ((dampingParam c) : ℂ) with hb
  have step_a : ∀ ξ : V, cexp (-b * (‖ξ‖) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ))) * measureFourier μ ξ) =
      ∫ x, cexp (-b * (‖ξ‖) ^ 2 + I * ((⟪z - x, ξ⟫ : ℝ))) ∂μ := by
    intro ξ
    unfold measureFourier
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.exp_add, ← Complex.exp_add, inner_sub_left, real_inner_comm,
      real_inner_comm ξ x]
    push_cast
    ring
  simp_rw [step_a]
  have hb0 : 0 < b.re := by exact dampingParam_pos hc
  have hG : Integrable (fun ξ : V => ‖cexp (-b * (‖ξ‖) ^ 2 + 0 * ((⟪(0 : V), ξ⟫ : ℝ)))‖) :=
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb0 0 0).norm
  have hint : Integrable (Function.uncurry fun ξ x =>
      cexp (-b * (‖ξ‖) ^ 2 + I * ((⟪z - x, ξ⟫ : ℝ)))) (volume.prod μ) := by
    have h2 : Integrable (fun p : V × V =>
        ‖cexp (-b * (‖p.1‖) ^ 2 + 0 * ((⟪(0 : V), p.1⟫ : ℝ)))‖ * (1))
        (volume.prod μ) := hG.mul_prod (integrable_const (1))
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · fun_prop
    · show ‖cexp (-b * (‖p.1‖ : ℂ) ^ 2 + I * ((⟪z - p.2, p.1⟫ : ℝ) : ℂ))‖ ≤
        ‖cexp (-b * (‖p.1‖ : ℂ) ^ 2 + 0 * ((⟪(0 : V), p.1⟫ : ℝ) : ℂ))‖ * 1
      rw [Complex.norm_exp, Complex.norm_exp]
      simp
  rw [integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [gaussian_inner_integral hc (z - x), Complex.ofReal_mul]

/-- The Gaussian-regularised density `μ * (Gaussian)`. -/
def regDensity (μ : Measure V) (c : ℝ) (z : V) : ℝ :=
  ∫ x, gaussPeak V c (z - x) ∂μ

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The regularised density is nonnegative. -/
lemma regDensity_nonneg (μ : Measure V) {c : ℝ} (hc : 0 ≤ c) (z : V) : 0 ≤ regDensity μ c z :=
  integral_nonneg fun _ => gaussPeak_nonneg hc _

/-- The Fourier-inversion integral `∫ e^{i⟨ξ,z⟩} φ(ξ) dξ`. -/
def invIntegral (φ : V → ℂ) (z : V) : ℂ :=
  ∫ ξ, cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * φ ξ

/-- The candidate density `(2π)^{-d} Re ∫ e^{i⟨ξ,z⟩} φ(ξ) dξ`. -/
def invDensity (μ : Measure V) (z : V) : ℝ :=
  ((2 * Real.pi) ^ finrank ℝ V)⁻¹ * (invIntegral (measureFourier μ) z).re

/-- The regularised density is the real part of the damped inversion integral. -/
lemma two_pi_pow_mul_regDensity (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (z : V) :
    ((2 * Real.pi) ^ finrank ℝ V : ℝ) * regDensity μ c z =
      (∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ)).re := by
  rw [regularized_eq μ hc z, integral_complex_ofReal, ← Complex.ofReal_mul]
  rfl

/-- The damped inversion integral converges to the inversion integral (dominated
convergence). -/
lemma tendsto_regularized (μ : Measure V) (hφ : Integrable (measureFourier μ)) (z : V) :
    Tendsto (fun c : ℝ => ∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ)) atTop
      (𝓝 (invIntegral (measureFourier μ) z)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖measureFourier μ ξ‖)
    ?_ ?_ hφ.norm ?_
  · refine Filter.Eventually.of_forall fun c => ?_
    fun_prop
  · filter_upwards [Ioi_mem_atTop (0)] with c hc
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [norm_mul, norm_mul, Complex.norm_exp (I * _)]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      zero_mul, mul_zero, Real.exp_zero, sub_self]
    nlinarith [norm_damp_le_one (V := V) hc ξ, norm_nonneg (measureFourier μ ξ)]
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : Tendsto (fun c : ℝ => cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2)) atTop
        (𝓝 1) := by
      have : Tendsto (fun c : ℝ => -((dampingParam c : ℝ)) * (‖ξ‖ : ℂ) ^ 2) atTop
          (𝓝 (-((0 : ℝ)) * (‖ξ‖) ^ 2)) :=
        ((Complex.continuous_ofReal.tendsto _).comp tendsto_dampingParam).neg.mul_const _
      simpa using this.cexp
    simpa [invIntegral] using h1.mul_const _

/-- The Gaussian profile has integral one. -/
lemma integral_peakProfile : ∫ w : V, peakProfile V w = 1 := by
  have hpi := Real.pi_pos
  unfold peakProfile
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
  nth_rewrite 2 [← pow_one Real.pi]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hpi, ← Real.rpow_mul hpi.le,
    ← Real.rpow_add hpi]
  norm_num

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Gaussian profile decays faster than any power at infinity. -/
lemma tendsto_norm_pow_mul_peakProfile :
    Tendsto (fun w : V => ‖w‖ ^ finrank ℝ V * peakProfile V w) (Bornology.cobounded V) (𝓝 0) := by
  have A : Tendsto (fun w ↦ Real.pi ^ 2 * ‖w‖ ^ 2) (Bornology.cobounded V) atTop := by
    rw [tendsto_const_mul_atTop_of_pos (by positivity)]
    apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank ℝ V / 2) 1
    zero_lt_one |>.comp A |>.const_mul (Real.pi ^ (-finrank ℝ V / 2 : ℝ))
  rw [mul_zero] at B
  convert! B using 2 with x
  simp only [Function.comp_apply, ← mul_assoc, ← Real.rpow_natCast, peakProfile]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul Real.pi_pos.le,
    ← Real.rpow_mul (norm_nonneg _), ← mul_assoc, ← Real.rpow_add Real.pi_pos]
  ring

/-- The shifted Gaussian peak kernel has integral one. -/
lemma integral_gaussPeak_sub {c : ℝ} (hc : 0 < c) (x : V) :
    ∫ z : V, gaussPeak V c (z - x) = 1 := by
  unfold gaussPeak
  rw [integral_sub_right_eq_self (fun z : V => c ^ finrank ℝ V * peakProfile V (c • z)) x,
    integral_const_mul,
    Measure.integral_comp_smul volume (fun z : V => peakProfile V z) c,
    integral_peakProfile, smul_eq_mul, mul_one, abs_of_pos (by positivity), mul_inv_cancel₀]
  positivity

/-- Approximate identity: Gaussian peaks converge on bounded continuous integrable functions. -/
lemma tendsto_peak_conv {ψ : V → ℝ} (hψ : Integrable ψ) (hψc : Continuous ψ) (x : V) :
    Tendsto (fun c : ℝ => ∫ z : V, gaussPeak V c (z - x) * ψ z) atTop (𝓝 (ψ x)) := by
  have := tendsto_integral_comp_smul_smul_of_integrable' (μ := volume)
    (φ := peakProfile V) peakProfile_nonneg integral_peakProfile
    tendsto_norm_pow_mul_peakProfile hψ hψc.continuousAt (x₀ := x)
  refine this.congr fun c => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul, gaussPeak]
  have h : ‖c • (x - z)‖ = ‖c • (z - x)‖ := by rw [norm_smul, norm_smul, norm_sub_rev]
  simp only [peakProfile, h]

omit [FiniteDimensional ℝ V] in
/-- The regularised density is continuous. -/
lemma continuous_regDensity (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 ≤ c) :
    Continuous (regDensity μ c) := by
  refine continuous_of_dominated
    (bound := fun _ => c ^ finrank ℝ V * Real.pi ^ (finrank ℝ V / 2 : ℝ))
    (fun z => ?_) (fun z => Filter.Eventually.of_forall fun x => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((continuous_gaussPeak c).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (gaussPeak_nonneg hc _)]
    exact gaussPeak_le hc _
  · exact (continuous_gaussPeak c).comp (continuous_id.sub continuous_const)

/-- Fubini: pairing a test function with the regularised density. -/
lemma integral_mul_regDensity (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c)
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    ∫ z, ψ z * regDensity μ c z = ∫ x, (∫ z, gaussPeak V c (z - x) * ψ z) ∂μ := by
  have hK := continuous_gaussPeak (V := V) c
  have hnorm : ∀ z, ∫ x, ‖ψ z * gaussPeak V c (z - x)‖ ∂μ = ‖ψ z‖ * regDensity μ c z := by
    intro z
    unfold regDensity
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [norm_mul, Real.norm_eq_abs (gaussPeak V c (z - x)),
      abs_of_nonneg (gaussPeak_nonneg hc.le _)]
  have hint : Integrable (Function.uncurry fun z x => ψ z * gaussPeak V c (z - x))
      (volume.prod μ) := by
    rw [integrable_prod_iff]
    · refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
      · refine Integrable.of_bound
          (C := ‖ψ z‖ * (c ^ finrank ℝ V * Real.pi ^ (finrank ℝ V / 2 : ℝ)))
          ((by fun_prop : Continuous fun x : V => ψ z * gaussPeak V c (z - x)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        show ‖ψ z * gaussPeak V c (z - x)‖ ≤ _
        rw [norm_mul, Real.norm_eq_abs (gaussPeak V c (z - x)),
          abs_of_nonneg (gaussPeak_nonneg hc.le _)]
        exact mul_le_mul_of_nonneg_left (gaussPeak_le hc.le _) (norm_nonneg _)
      · simp only [Function.uncurry_apply_pair]
        simp_rw [hnorm]
        exact (hψ.norm.mul (continuous_regDensity μ hc.le)).integrable_of_hasCompactSupport
          (hψs.norm.mul_right)
    fun_prop
  have := integral_integral_swap hint
  calc ∫ z, ψ z * ∫ x, gaussPeak V c (z - x) ∂μ
      = ∫ z, ∫ x, ψ z * gaussPeak V c (z - x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ x, (∫ z, ψ z * gaussPeak V c (z - x)) ∂μ := this
    _ = _ := by
        grind

/-- The regularised density converges weakly to `μ` against compactly supported
continuous test functions. -/
lemma tendsto_integral_mul_regDensity (μ : Measure V) [IsFiniteMeasure μ]
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Tendsto (fun c : ℝ => ∫ z, ψ z * regDensity μ c z) atTop (𝓝 (∫ x, ψ x ∂μ)) := by
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψs
  obtain ⟨B, hB⟩ := hψs.exists_bound_of_continuous hψ
  have hlim : Tendsto (fun c : ℝ => ∫ x, (∫ z, gaussPeak V c (z - x) * ψ z) ∂μ) atTop
      (𝓝 (∫ x, ψ x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
      (integrable_const _) ?_
    · refine Filter.Eventually.of_forall fun c => ?_
      have hK := continuous_gaussPeak (V := V) c
      exact (StronglyMeasurable.integral_prod_right
        (f := fun x z : V => gaussPeak V c (z - x) * ψ z)
        (by fun_prop)).aestronglyMeasurable
    · filter_upwards [Ioi_mem_atTop (0)] with c hc
      refine Filter.Eventually.of_forall fun x => ?_
      have hI : Integrable (fun z : V => gaussPeak V c (z - x)) :=
        integrable_of_integral_eq_one (integral_gaussPeak_sub hc x)
      calc ‖∫ z, gaussPeak V c (z - x) * ψ z‖
          ≤ ∫ z, B * gaussPeak V c (z - x) := by
            refine norm_integral_le_of_norm_le (hI.const_mul B)
              (Filter.Eventually.of_forall fun z => ?_)
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussPeak_nonneg hc.le _), mul_comm]
            exact mul_le_mul_of_nonneg_right (hB z) (gaussPeak_nonneg hc.le _)
        _ = B := by rw [integral_const_mul, integral_gaussPeak_sub hc x, mul_one]
    · exact Filter.Eventually.of_forall fun x => tendsto_peak_conv hψi hψ x
  refine hlim.congr' ?_
  filter_upwards [Ioi_mem_atTop (0)] with c hc
  exact (integral_mul_regDensity μ hc hψ hψs).symm

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Pointwise domination of the damped inversion integrand. -/
lemma norm_regularized_integrand_le (μ : Measure V) {c : ℝ} (hc : 0 < c) (z ξ : V) :
    ‖cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ)‖ ≤ ‖measureFourier μ ξ‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp (I * _)]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    zero_mul, mul_zero, Real.exp_zero, sub_self]
  nlinarith [norm_damp_le_one (V := V) hc ξ, norm_nonneg (measureFourier μ ξ)]

/-- Uniform bound `(2π)^{-d} ‖μ̂‖₁` for the regularised density. -/
lemma regDensity_le (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    {c : ℝ} (hc : 0 < c) (z : V) :
    regDensity μ c z ≤ ((2 * Real.pi) ^ finrank ℝ V)⁻¹ * ∫ ξ, ‖measureFourier μ ξ‖ := by
  have hpos : 0 < (2 * Real.pi) ^ finrank ℝ V := by positivity
  have h1 := two_pi_pow_mul_regDensity μ hc z
  have h2 : (∫ ξ : V, cexp (-((dampingParam c : ℝ)) * (‖ξ‖) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ))) * measureFourier μ ξ)).re ≤ ∫ ξ, ‖measureFourier μ ξ‖ :=
    (Complex.re_le_norm _).trans
      (norm_integral_le_of_norm_le hφ.norm
        (Filter.Eventually.of_forall fun ξ => norm_regularized_integrand_le μ hc z ξ))
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-- The regularised density converges pointwise to the inversion density. -/
lemma tendsto_regDensity (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    (z : V) : Tendsto (fun c : ℝ => regDensity μ c z) atTop (𝓝 (invDensity μ z)) := by
  have h := ((Complex.continuous_re.tendsto _).comp (tendsto_regularized μ hφ z)).const_mul
    (((2 * Real.pi) ^ finrank ℝ V)⁻¹)
  refine h.congr' ?_
  filter_upwards [Ioi_mem_atTop (0)] with c hc
  have hpos : 0 < (2 * Real.pi) ^ finrank ℝ V := by positivity
  simp only [Function.comp_apply]
  rw [← two_pi_pow_mul_regDensity μ hc z, inv_mul_cancel_left₀ hpos.ne']

/-- The inversion density is nonnegative. -/
lemma invDensity_nonneg (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    (z : V) : 0 ≤ invDensity μ z :=
  ge_of_tendsto (tendsto_regDensity μ hφ z)
    (by filter_upwards [Ioi_mem_atTop (0)] with c hc using regDensity_nonneg μ hc.le z)

/-- The inversion density is bounded by `(2π)^{-d} ‖μ̂‖₁`. -/
lemma invDensity_le (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    (z : V) : invDensity μ z ≤ ((2 * Real.pi) ^ finrank ℝ V)⁻¹ * ∫ ξ, ‖measureFourier μ ξ‖ :=
  le_of_tendsto (tendsto_regDensity μ hφ z)
    (by filter_upwards [Ioi_mem_atTop (0)] with c hc using regDensity_le μ hφ hc z)

/-- The inversion integral is continuous. -/
lemma continuous_invIntegral (μ : Measure V) (hφ : Integrable (measureFourier μ)) :
    Continuous (invIntegral (measureFourier μ)) := by
  refine continuous_of_dominated (bound := fun ξ => ‖measureFourier μ ξ‖) (fun z => ?_)
    (fun z => Filter.Eventually.of_forall fun ξ => ?_) hφ.norm
    (Filter.Eventually.of_forall fun ξ => ?_)
  · fun_prop
  · simp
  fun_prop

/-- The inversion density is continuous. -/
lemma continuous_invDensity (μ : Measure V) (hφ : Integrable (measureFourier μ)) :
    Continuous (invDensity μ) := continuous_const.mul (Complex.continuous_re.comp (continuous_invIntegral μ hφ))

/-- The regularised density converges to the inversion density against compactly
supported test functions (dominated convergence). -/
lemma tendsto_integral_mul_regDensity_inv (μ : Measure V) [IsFiniteMeasure μ]
    (hφ : Integrable (measureFourier μ)) {ψ : V → ℝ} (hψ : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    Tendsto (fun c : ℝ => ∫ z, ψ z * regDensity μ c z) atTop
      (𝓝 (∫ z, ψ z * invDensity μ z)) := by
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψs
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖ψ z‖ * (((2 * Real.pi) ^ finrank ℝ V)⁻¹ * ∫ ξ, ‖measureFourier μ ξ‖)) ?_ ?_
    (hψi.norm.mul_const _) ?_
  · filter_upwards [Ioi_mem_atTop (0)] with c hc
    exact (hψ.mul (continuous_regDensity μ hc.le)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop (0)] with c hc
    refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs (regDensity μ c z),
      abs_of_nonneg (regDensity_nonneg μ hc.le z)]
    exact mul_le_mul_of_nonneg_left (regDensity_le μ hφ hc z) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun z => (tendsto_regDensity μ hφ z).const_mul (ψ z)

/-- `μ` and the inversion density have the same integral against compactly supported
continuous functions. -/
theorem integral_mul_invDensity_eq (μ : Measure V) [IsFiniteMeasure μ]
    (hφ : Integrable (measureFourier μ)) {ψ : V → ℝ} (hψ : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    ∫ x, ψ x ∂μ = ∫ z, ψ z * invDensity μ z :=
  tendsto_nhds_unique (tendsto_integral_mul_regDensity μ hψ hψs)
    (tendsto_integral_mul_regDensity_inv μ hφ hψ hψs)

/-- **Fourier inversion for finite measures.**  A finite measure on `V` with integrable Fourier
transform equals Lebesgue measure with the (nonnegative, continuous) density `invDensity μ`. -/
theorem eq_withDensity_invDensity (μ : Measure V) [IsFiniteMeasure μ]
    (hφ : Integrable (measureFourier μ)) :
    μ = volume.withDensity (fun z => ENNReal.ofReal (invDensity μ z)) := by
  have hmeas : Measurable (invDensity μ) := (continuous_invDensity μ hφ).measurable
  set ν : Measure V := volume.withDensity (fun z => ENNReal.ofReal (invDensity μ z)) with hν
  have : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    calc ν K ≤ ∫⁻ z in K, ENNReal.ofReal (((2 * Real.pi) ^ finrank ℝ V)⁻¹ *
          ∫ ξ, ‖measureFourier μ ξ‖) := by
          rw [withDensity_apply _ hK.measurableSet]
          exact setLIntegral_mono measurable_const fun z _ =>
            ENNReal.ofReal_le_ofReal (invDensity_le μ hφ z)
      _ < ∞ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  rw [integral_withDensity_eq_integral_toReal_smul (hmeas.ennreal_ofReal)
    (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (invDensity_nonneg μ hφ _), smul_eq_mul]
  have := integral_mul_invDensity_eq μ hφ f.continuous f.hasCompactSupport
  simp only [mul_comm (invDensity μ _)]
  omega

end Main

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction
