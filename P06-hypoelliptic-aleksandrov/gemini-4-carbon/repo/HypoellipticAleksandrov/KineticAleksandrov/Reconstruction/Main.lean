module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import PDEFoundation.Ambient.EuclideanNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction
section
open MeasureTheory Complex Filter Topology Module
open scoped RealInnerProductSpace ENNReal

section Peak


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gaussian profile `π^{d/2} e^{-π²‖w‖²}` of integral one. -/
noncomputable def peakProfile (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (w : V) : ℝ :=
  Real.pi ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-Real.pi ^ 2 * ‖w‖ ^ 2)

/-- Gaussian peak kernel `c^d π^{d/2} e^{-π² c² ‖u‖²}`. -/
noncomputable def gaussPeak (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (c : ℝ) (u : V) : ℝ :=
  c ^ finrank ℝ V * peakProfile V (c • u)

/-- Damping parameter. -/
noncomputable def dampingParam (c : ℝ) : ℝ := (4 * Real.pi ^ 2 * c ^ 2)⁻¹

/-- The damping parameter is positive for `c > 0`. -/
lemma dampingParam_pos {c : ℝ} (hc : 0 < c) : 0 < dampingParam c := by
  have := Real.pi_pos
  unfold dampingParam
  positivity


/-- The damping parameter tends to zero as `c → ∞`. -/
lemma tendsto_dampingParam : Tendsto dampingParam atTop (𝓝 0) := by
  have h : Tendsto (fun c => 4 * Real.pi ^ 2 * c ^ 2) atTop atTop := by
    have := Real.pi_pos
    exact Tendsto.const_mul_atTop (by positivity) (tendsto_pow_atTop two_ne_zero)
  exact tendsto_inv_atTop_zero.comp h

/-- The Gaussian damping factor has modulus at most one. -/
lemma norm_damp_le_one {V : Type*} [NormedAddCommGroup V] {c : ℝ} (hc : 0 < c) (ξ : V) :
    ‖cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have := dampingParam_pos hc
  simp
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
  unfold gaussPeak peakProfile
  have h : Real.exp (-Real.pi ^ 2 * ‖c • u‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖c • u‖, sq_nonneg Real.pi]
  have h0 : 0 ≤ Real.pi ^ (finrank ℝ V / 2 : ℝ) := by positivity
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
noncomputable def measureFourier (μ : Measure V) (ξ : V) : ℂ :=
  ∫ x, cexp (-((⟪ξ, x⟫ : ℝ) * I)) ∂μ


/-- Fubini: the Gaussian-damped inversion integral is `(2π)^d` times the Gaussian
regularisation `∫ gaussPeak c (z - x) dμ(x)` of `μ`. -/
lemma regularized_eq (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (z : V) :
    ∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ) =
      ((2 * Real.pi) ^ finrank ℝ V : ℝ) * ∫ x, ((gaussPeak V c (z - x) : ℝ) : ℂ) ∂μ  := by
  have gaussian_inner_integral (w : V) :
      ∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2 + I * ((⟪w, ξ⟫ : ℝ) : ℂ)) =
      (((2 * Real.pi) ^ finrank ℝ V * gaussPeak V c w : ℝ) : ℂ) := by
    have peak_const (n : ℕ) :
        ((2 * Real.pi) ^ n)⁻¹ * (Real.pi / dampingParam c) ^ (n / 2 : ℝ) =
        c ^ n * Real.pi ^ (n / 2 : ℝ) := by
      have hpi := Real.pi_pos
      have h1 : Real.pi / dampingParam c = (2 * Real.pi * c) ^ 2 * Real.pi := by
        unfold dampingParam
        field_simp
        norm_num
      have h2 : ((2 * Real.pi * c) ^ 2 * Real.pi) ^ (n / 2 : ℝ) =
          (2 * Real.pi * c) ^ n * Real.pi ^ (n / 2 : ℝ) := by
        rw [Real.mul_rpow (by positivity) hpi.le, ← Real.rpow_natCast (2 * Real.pi * c) 2,
          ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (2 * Real.pi * c) n]
        congr 2
        push_cast
        ring
      rw [h1, h2]
      have : (2 * Real.pi) ^ n ≠ 0 := by positivity
      field_simp
      ring
    have hpi := Real.pi_pos
    have hb : 0 < (((dampingParam c : ℝ) : ℂ)).re := by
      rw [Complex.ofReal_re]; exact dampingParam_pos hc
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb I w]
    have h1 : ((Real.pi : ℂ) / ((dampingParam c : ℝ) : ℂ)) ^ ((finrank ℝ V : ℂ) / 2) =
        (((Real.pi / dampingParam c) ^ ((finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (div_nonneg hpi.le (dampingParam_pos hc).le)]
      push_cast
      rfl
    have h2 : I ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * ((dampingParam c : ℝ) : ℂ)) =
        ((-Real.pi ^ 2 * ‖c • w‖ ^ 2 : ℝ) : ℂ) := by
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      unfold dampingParam
      push_cast
      field_simp
      simp
    rw [h1, h2, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
    congr 1
    unfold gaussPeak peakProfile
    have hA : (Real.pi / dampingParam c) ^ ((finrank ℝ V : ℝ) / 2) =
        (2 * Real.pi) ^ finrank ℝ V * (c ^ finrank ℝ V * Real.pi ^ ((finrank ℝ V : ℝ) / 2)) := by
      rw [← (peak_const (finrank ℝ V)), mul_inv_cancel_left₀ (by positivity)]
    rw [hA]
    ring
  set b : ℂ := ((dampingParam c : ℝ) : ℂ) with hb
  have step_a : ∀ ξ : V, cexp (-b * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ) =
      ∫ x, cexp (-b * (‖ξ‖ : ℂ) ^ 2 + I * ((⟪z - x, ξ⟫ : ℝ) : ℂ)) ∂μ := by
    intro ξ
    unfold measureFourier
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Complex.exp_add, ← Complex.exp_add, inner_sub_left, real_inner_comm ξ z,
      real_inner_comm ξ x]
    congr 1
    push_cast
    ring
  simp_rw [step_a]
  have hb0 : 0 < b.re := by rw [hb, Complex.ofReal_re]; exact dampingParam_pos hc
  have hG : Integrable (fun ξ : V => ‖cexp (-b * (‖ξ‖ : ℂ) ^ 2 + 0 * ((⟪0, ξ⟫ : ℝ) : ℂ))‖) :=
    (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb0 0 0).norm
  have hint : Integrable (Function.uncurry fun (ξ : V) (x : V) =>
      cexp (-b * (‖ξ‖ : ℂ) ^ 2 + I * ((⟪z - x, ξ⟫ : ℝ) : ℂ))) (volume.prod μ) := by
    have h2 : Integrable (fun p : V × V =>
        ‖cexp (-b * (‖p.1‖ : ℂ) ^ 2 + 0 * ((⟪0, p.1⟫ : ℝ) : ℂ))‖ * 1)
        (volume.prod μ) := hG.mul_prod (integrable_const 1)
    refine h2.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (by fun_prop : Continuous fun p : V × V => cexp (-b * (‖p.1‖ : ℂ) ^ 2 +
          I * ((⟪z - p.2, p.1⟫ : ℝ) : ℂ))).aestronglyMeasurable
    · show ‖cexp (-b * (‖p.1‖ : ℂ) ^ 2 + I * ((⟪z - p.2, p.1⟫ : ℝ) : ℂ))‖ ≤
        ‖cexp (-b * (‖p.1‖ : ℂ) ^ 2 + 0 * ((⟪0, p.1⟫ : ℝ) : ℂ))‖ * 1
      rw [Complex.norm_exp, Complex.norm_exp, mul_one]
      apply le_of_eq
      congr 1
      simp [hb, sq]
  rw [integral_integral_swap hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [hb, gaussian_inner_integral (z - x), Complex.ofReal_mul]

/-- The Gaussian-regularised density `μ * (Gaussian)`. -/
noncomputable def regDensity (μ : Measure V) (c : ℝ) (z : V) : ℝ :=
  ∫ x, gaussPeak V c (z - x) ∂μ

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The regularised density is nonnegative. -/
lemma regDensity_nonneg (μ : Measure V) {c : ℝ} (hc : 0 ≤ c) (z : V) : 0 ≤ regDensity μ c z :=
  integral_nonneg fun _ => gaussPeak_nonneg hc _

/-- The Fourier-inversion integral `∫ e^{i⟨ξ,z⟩} φ(ξ) dξ`. -/
noncomputable def invIntegral (φ : V → ℂ) (z : V) : ℂ :=
  ∫ ξ, cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * φ ξ

/-- The candidate density `(2π)^{-d} Re ∫ e^{i⟨ξ,z⟩} φ(ξ) dξ`. -/
noncomputable def invDensity (μ : Measure V) (z : V) : ℝ :=
  ((2 * Real.pi) ^ finrank ℝ V)⁻¹ * (invIntegral (measureFourier μ) z).re

/-- The regularised density is the real part of the damped inversion integral. -/
lemma two_pi_pow_mul_regDensity (μ : Measure V) [IsFiniteMeasure μ] {c : ℝ} (hc : 0 < c) (z : V) :
    ((2 * Real.pi) ^ finrank ℝ V : ℝ) * regDensity μ c z =
      (∫ ξ : V, cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ)).re := by
  rw [regularized_eq μ hc z, integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
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
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul hφ.1)
  · filter_upwards [Ioi_mem_atTop 0] with c hc
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [norm_mul, norm_mul, Complex.norm_exp (I * _)]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, Real.exp_zero, one_mul, sub_self]
    nlinarith [norm_damp_le_one (V := V) hc ξ, norm_nonneg (measureFourier μ ξ)]
  · refine Filter.Eventually.of_forall fun ξ => ?_
    have h1 : Tendsto (fun c => cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2)) atTop
        (𝓝 1) := by
      have : Tendsto (fun c => -((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) atTop
          (𝓝 (-(0 : ℂ) * (‖ξ‖ : ℂ) ^ 2)) :=
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
  ring_nf
  exact Real.rpow_zero _

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Gaussian profile decays faster than any power at infinity. -/
lemma tendsto_norm_pow_mul_peakProfile :
    Tendsto (fun w : V => ‖w‖ ^ finrank ℝ V * peakProfile V w) (Bornology.cobounded V) (𝓝 0) := by
  have A : Tendsto (fun (w : V) ↦ Real.pi ^ 2 * ‖w‖ ^ 2) (Bornology.cobounded V) atTop := by
    rw [tendsto_const_mul_atTop_of_pos (by positivity)]
    apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
  have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank ℝ V / 2) 1
    zero_lt_one |>.comp A |>.const_mul (Real.pi ^ (-finrank ℝ V / 2 : ℝ))
  rw [mul_zero] at B
  convert! B using 2 with x
  simp only [neg_mul, one_mul, Function.comp_apply, ← mul_assoc, ← Real.rpow_natCast, peakProfile]
  congr 1
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul Real.pi_pos.le,
    ← Real.rpow_mul (norm_nonneg _), ← mul_assoc, ← Real.rpow_add Real.pi_pos, mul_comm]
  congr <;> ring

/-- The shifted Gaussian peak kernel has integral one. -/
lemma integral_gaussPeak_sub {c : ℝ} (hc : 0 < c) (x : V) :
    ∫ z : V, gaussPeak V c (z - x) = 1 := by
  unfold gaussPeak
  rw [integral_sub_right_eq_self (fun z => c ^ finrank ℝ V * peakProfile V (c • z)) x,
    integral_const_mul,
    Measure.integral_comp_smul (volume : Measure V) (fun z => peakProfile V z) c,
    integral_peakProfile, smul_eq_mul, mul_one, abs_of_pos (by positivity), mul_inv_cancel₀]
  positivity

/-- Approximate identity: Gaussian peaks converge on bounded continuous integrable functions. -/
lemma tendsto_peak_conv {ψ : V → ℝ} (hψ : Integrable ψ) (hψc : Continuous ψ) (x : V) :
    Tendsto (fun c : ℝ => ∫ z : V, gaussPeak V c (z - x) * ψ z) atTop (𝓝 (ψ x)) := by
  have := tendsto_integral_comp_smul_smul_of_integrable' (μ := (volume : Measure V))
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
  unfold regDensity
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
  have hint : Integrable (Function.uncurry fun (z : V) (x : V) => ψ z * gaussPeak V c (z - x))
      (volume.prod μ) := by
    rw [integrable_prod_iff]
    · refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
      · refine Integrable.of_bound
          (C := ‖ψ z‖ * (c ^ finrank ℝ V * Real.pi ^ (finrank ℝ V / 2 : ℝ)))
          ((by fun_prop : Continuous fun x => ψ z * gaussPeak V c (z - x)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x => ?_)
        show ‖ψ z * gaussPeak V c (z - x)‖ ≤ _
        rw [norm_mul, Real.norm_eq_abs (gaussPeak V c (z - x)),
          abs_of_nonneg (gaussPeak_nonneg hc.le _)]
        exact mul_le_mul_of_nonneg_left (gaussPeak_le hc.le _) (norm_nonneg _)
      · simp only [Function.uncurry_apply_pair]
        simp_rw [hnorm]
        exact (hψ.norm.mul (continuous_regDensity μ hc.le)).integrable_of_hasCompactSupport
          (hψs.norm.mul_right)
    · exact (by fun_prop : Continuous fun p : V × V =>
        ψ p.1 * gaussPeak V c (p.1 - p.2)).aestronglyMeasurable
  have := integral_integral_swap hint
  unfold regDensity
  calc ∫ z, ψ z * ∫ x, gaussPeak V c (z - x) ∂μ
      = ∫ z, ∫ x, ψ z * gaussPeak V c (z - x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ x, (∫ z, ψ z * gaussPeak V c (z - x)) ∂μ := this
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)

/-- The regularised density converges weakly to `μ` against compactly supported
continuous test functions. -/
lemma tendsto_integral_mul_regDensity (μ : Measure V) [IsFiniteMeasure μ]
    {ψ : V → ℝ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ) :
    Tendsto (fun c : ℝ => ∫ z, ψ z * regDensity μ c z) atTop (𝓝 (∫ x, ψ x ∂μ)) := by
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψs
  obtain ⟨B, hB⟩ := hψs.exists_bound_of_continuous hψ
  have hlim : Tendsto (fun c => ∫ x, (∫ z, gaussPeak V c (z - x) * ψ z) ∂μ) atTop
      (𝓝 (∫ x, ψ x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
      (integrable_const _) ?_
    · refine Filter.Eventually.of_forall fun c => ?_
      have hK := continuous_gaussPeak (V := V) c
      exact (StronglyMeasurable.integral_prod_right
        (f := fun x z => gaussPeak V c (z - x) * ψ z)
        (by exact (by fun_prop : Continuous fun p : V × V =>
          gaussPeak V c (p.2 - p.1) * ψ p.2).stronglyMeasurable)).aestronglyMeasurable
    · filter_upwards [Ioi_mem_atTop 0] with c hc
      refine Filter.Eventually.of_forall fun x => ?_
      calc ‖∫ z, gaussPeak V c (z - x) * ψ z‖
          ≤ ∫ z, B * gaussPeak V c (z - x) := by
            refine norm_integral_le_of_norm_le ((integrable_of_integral_eq_one (integral_gaussPeak_sub hc x)).const_mul B)
              (Filter.Eventually.of_forall fun z => ?_)
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gaussPeak_nonneg hc.le _), mul_comm]
            exact mul_le_mul_of_nonneg_right (hB z) (gaussPeak_nonneg hc.le _)
        _ = B := by rw [integral_const_mul, integral_gaussPeak_sub hc x, mul_one]
    · exact Filter.Eventually.of_forall fun x => tendsto_peak_conv hψi hψ x
  refine hlim.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with c hc
  exact (integral_mul_regDensity μ hc hψ hψs).symm

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Pointwise domination of the damped inversion integrand. -/
lemma norm_regularized_integrand_le (μ : Measure V) {c : ℝ} (hc : 0 < c) (z ξ : V) :
    ‖cexp (-((dampingParam c : ℝ) : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        (cexp (I * ((⟪ξ, z⟫ : ℝ) : ℂ)) * measureFourier μ ξ)‖ ≤ ‖measureFourier μ ξ‖ := by
  rw [norm_mul, norm_mul, Complex.norm_exp (I * _)]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, Real.exp_zero, one_mul, sub_self]
  nlinarith [norm_damp_le_one (V := V) hc ξ, norm_nonneg (measureFourier μ ξ)]

/-- Uniform bound `(2π)^{-d} ‖μ̂‖₁` for the regularised density. -/
lemma regDensity_le (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    {c : ℝ} (hc : 0 < c) (z : V) :
    regDensity μ c z ≤ ((2 * Real.pi) ^ finrank ℝ V)⁻¹ * ∫ ξ, ‖measureFourier μ ξ‖ := by
  have hpos : 0 < (2 * Real.pi) ^ finrank ℝ V := by have := Real.pi_pos; positivity
  have h2 :=
    (Complex.re_le_norm _).trans
      (norm_integral_le_of_norm_le hφ.norm
        (Filter.Eventually.of_forall fun ξ => norm_regularized_integrand_le μ hc z ξ))
  rw [← (two_pi_pow_mul_regDensity μ hc z)] at h2
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith

/-- The regularised density converges pointwise to the inversion density. -/
lemma tendsto_regDensity (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    (z : V) : Tendsto (fun c : ℝ => regDensity μ c z) atTop (𝓝 (invDensity μ z)) := by
  have h := ((Complex.continuous_re.tendsto _).comp (tendsto_regularized μ hφ z)).const_mul
    (((2 * Real.pi) ^ finrank ℝ V)⁻¹)
  refine h.congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with c hc
  have hpos : 0 < (2 * Real.pi) ^ finrank ℝ V := by have := Real.pi_pos; positivity
  simp only [Function.comp_apply]
  rw [← two_pi_pow_mul_regDensity μ hc z, inv_mul_cancel_left₀ hpos.ne']

/-- The inversion density is nonnegative. -/
lemma invDensity_nonneg (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    (z : V) : 0 ≤ invDensity μ z :=
  ge_of_tendsto (tendsto_regDensity μ hφ z)
    (by filter_upwards [Ioi_mem_atTop 0] with c hc using regDensity_nonneg μ hc.le z)

/-- The inversion density is bounded by `(2π)^{-d} ‖μ̂‖₁`. -/
lemma invDensity_le (μ : Measure V) [IsFiniteMeasure μ] (hφ : Integrable (measureFourier μ))
    (z : V) : invDensity μ z ≤ ((2 * Real.pi) ^ finrank ℝ V)⁻¹ * ∫ ξ, ‖measureFourier μ ξ‖ :=
  le_of_tendsto (tendsto_regDensity μ hφ z)
    (by filter_upwards [Ioi_mem_atTop 0] with c hc using regDensity_le μ hφ hc z)

/-- The inversion integral is continuous. -/
lemma continuous_invIntegral (μ : Measure V) (hφ : Integrable (measureFourier μ)) :
    Continuous (invIntegral (measureFourier μ)) := by
  unfold invIntegral
  refine continuous_of_dominated (bound := fun ξ => ‖measureFourier μ ξ‖) (fun z => ?_)
    (fun z => Filter.Eventually.of_forall fun ξ => ?_) hφ.norm
    (Filter.Eventually.of_forall fun ξ => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hφ.1
  · rw [norm_mul, Complex.norm_exp]
    simp
  · fun_prop

/-- The inversion density is continuous. -/
lemma continuous_invDensity (μ : Measure V) (hφ : Integrable (measureFourier μ)) :
    Continuous (invDensity μ) := by
  unfold invDensity
  exact continuous_const.mul (Complex.continuous_re.comp (continuous_invIntegral μ hφ))

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
  · filter_upwards [Ioi_mem_atTop 0] with c hc
    exact (hψ.mul (continuous_regDensity μ hc.le)).aestronglyMeasurable
  · filter_upwards [Ioi_mem_atTop 0] with c hc
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
  set ν : Measure V := volume.withDensity (fun z => ENNReal.ofReal (invDensity μ z)) with hν
  have : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    calc ν K ≤ ∫⁻ z in K, ENNReal.ofReal (((2 * Real.pi) ^ finrank ℝ V)⁻¹ *
          ∫ ξ, ‖measureFourier μ ξ‖) := by
          rw [hν, withDensity_apply _ hK.measurableSet]
          exact setLIntegral_mono measurable_const fun z _ =>
            ENNReal.ofReal_le_ofReal (invDensity_le μ hφ z)
      _ < ∞ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  rw [hν, integral_withDensity_eq_integral_toReal_smul (((continuous_invDensity μ hφ).measurable).ennreal_ofReal)
    (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (invDensity_nonneg μ hφ _), smul_eq_mul]
  have := integral_mul_invDensity_eq μ hφ f.continuous f.hasCompactSupport
  simp only [mul_comm (invDensity μ _)]
  exact this

end Main

end
section
section
open MeasureTheory Complex Filter Topology
open scoped ENNReal

variable {d : ℕ}

/-- The Fourier transform `ξ ↦ ∫ e^{-i ξ·x} dμ(x)` of a measure on `ℝ^d`. -/
def vecFourier (μ : Measure (PDE.Vec d)) (ξ : PDE.Vec d) : ℂ :=
  ∫ x, cexp (-((PDE.vecDot ξ x : ℝ) * I)) ∂μ

/-- The Fourier-inversion integral `∫ e^{i ξ·z} φ(ξ) dξ` on `ℝ^d`. -/
def vecInvIntegral (φ : PDE.Vec d → ℂ) (z : PDE.Vec d) : ℂ :=
  ∫ ξ, cexp (I * ((PDE.vecDot ξ z : ℝ) : ℂ)) * φ ξ

/-- The inversion density `(2π)^{-d} Re ∫ e^{i ξ·z} μ̂(ξ) dξ` of a measure on `ℝ^d`. -/
def vecInvDensity (μ : Measure (PDE.Vec d)) (z : PDE.Vec d) : ℝ :=
  ((2 * Real.pi) ^ d)⁻¹ * (vecInvIntegral (vecFourier μ) z).re

/-- The coordinate equivalence `ℝ^d ≃ EuclideanSpace ℝ (Fin d)`. -/
abbrev toEuclid (d : ℕ) : PDE.Vec d ≃ᵐ EuclideanSpace ℝ (Fin d) :=
  MeasurableEquiv.toLp 2 (PDE.Vec d)

/-- The Euclidean inner product of coordinate vectors is `PDE.vecDot`. -/
lemma inner_toLp (ξ x : PDE.Vec d) :
    inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 x) = PDE.vecDot ξ x := by
  simp
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The Fourier transform on `ℝ^d` agrees with that of the pushforward to Euclidean space. -/
lemma vecFourier_eq (μ : Measure (PDE.Vec d)) (ξ : PDE.Vec d) :
    measureFourier (μ.map (toEuclid d)) (WithLp.toLp 2 ξ) = vecFourier μ ξ := by
  unfold measureFourier vecFourier
  rw [(toEuclid d).measurableEmbedding.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [toEuclid, MeasurableEquiv.toLp_apply, inner_toLp]

/-- The inversion integral agrees with that of the pushforward to Euclidean space. -/
lemma invIntegral_eq (μ : Measure (PDE.Vec d)) (z : PDE.Vec d) :
    invIntegral (measureFourier (μ.map (toEuclid d))) (WithLp.toLp 2 z) =
      vecInvIntegral (vecFourier μ) z := by
  unfold invIntegral vecInvIntegral
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (toEuclid d).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [inner_toLp, vecFourier_eq]

/-- The inversion density agrees with that of the pushforward to Euclidean space. -/
lemma invDensity_eq (μ : Measure (PDE.Vec d)) (z : PDE.Vec d) :
    invDensity (μ.map (toEuclid d)) (WithLp.toLp 2 z) = vecInvDensity μ z := by
  unfold invDensity vecInvDensity
  rw [invIntegral_eq, finrank_euclideanSpace_fin]

/-- Integrability of the Fourier transform is preserved by the coordinate equivalence. -/
lemma integrable_vecFourier_iff (μ : Measure (PDE.Vec d)) :
    Integrable (measureFourier (μ.map (toEuclid d))) ↔ Integrable (vecFourier μ) := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integrable_comp_emb
    (toEuclid d).measurableEmbedding]
  refine integrable_congr (Filter.Eventually.of_forall fun ξ => ?_)
  exact vecFourier_eq μ ξ

/-- The `L^1` norm of the Fourier transform is preserved by the coordinate equivalence. -/
lemma integral_norm_vecFourier (μ : Measure (PDE.Vec d)) :
    ∫ ξ, ‖measureFourier (μ.map (toEuclid d)) ξ‖ = ∫ ξ, ‖vecFourier μ ξ‖ := by
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp (toEuclid d).measurableEmbedding]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
    simp only [vecFourier_eq])

section Inversion

variable (μ : Measure (PDE.Vec d)) [IsFiniteMeasure μ] (hφ : Integrable (vecFourier μ))
include hφ


/-- The inversion density is bounded by `(2π)^{-d} ‖μ̂‖₁`. -/
theorem vecInvDensity_le (z : PDE.Vec d) :
    vecInvDensity μ z ≤ ((2 * Real.pi) ^ d)⁻¹ * ∫ ξ, ‖vecFourier μ ξ‖ := by
  have h := invDensity_le (μ.map (toEuclid d)) ((integrable_vecFourier_iff μ).2 hφ)
    (WithLp.toLp 2 z)
  rwa [invDensity_eq, integral_norm_vecFourier, finrank_euclideanSpace_fin] at h

/-- Fourier inversion on `ℝ^d`: a finite measure with integrable Fourier transform has the
density `vecInvDensity μ` with respect to Lebesgue measure. -/
theorem eq_withDensity_vecInvDensity :
    μ = volume.withDensity (fun z => ENNReal.ofReal (vecInvDensity μ z)) := by
  ext S hS
  have he := (toEuclid d).measurableEmbedding
  have h1 : μ S = (μ.map (toEuclid d)) (toEuclid d '' S) := by
    rw [he.map_apply, (toEuclid d).injective.preimage_image]
  rw [h1, (eq_withDensity_invDensity (μ.map (toEuclid d)) ((integrable_vecFourier_iff μ).2 hφ)), withDensity_apply _ (he.measurableSet_image.2 hS), withDensity_apply _ hS]
  calc ∫⁻ a in toEuclid d '' S, ENNReal.ofReal (invDensity (μ.map (toEuclid d)) a)
      = ∫⁻ a in S, ENNReal.ofReal (invDensity (μ.map (toEuclid d)) (toEuclid d a)) :=
        ((PiLp.volume_preserving_toLp (Fin d)).setLIntegral_comp_emb he
          (fun a => ENNReal.ofReal (invDensity (μ.map (toEuclid d)) a)) S).symm
    _ = _ := setLIntegral_congr_fun hS fun z _ => by
        simp only [toEuclid, MeasurableEquiv.toLp_apply, invDensity_eq]

end Inversion

end
open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The Fourier transform `ξ ↦ ∫ e^{-i ξ·z} π_y(dz)` of the fibre measure `κ y`. -/
def fiberFourier (κ : Kernel Y (PDE.Vec d)) (ξ : PDE.Vec d) (y : Y) : ℂ :=
  ∫ z, cexp (-((PDE.vecDot ξ z : ℝ) * I)) ∂(κ y)

/-- The fibre representative `k̃^ξ(y) = g(y) ∫ e^{-i ξ·z} π_y(dz)` of the Fourier-marginal
density. -/
def fiberDensity (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (ξ : PDE.Vec d) (y : Y) : ℂ :=
  ((g y).toReal : ℂ) * fiberFourier κ ξ y

/-- The fibre height `H(y) = (2π)^{-d} ∫ |k̃^ξ(y)| dξ`. -/
def fiberHeight (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (y : Y) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) * ∫⁻ ξ, ‖fiberDensity g κ ξ y‖ₑ

/-- The character `ξ ↦ e^{-i ξ·z}` is continuous. -/
lemma continuous_exp_vecDot (z : PDE.Vec d) :
    Continuous fun ξ : PDE.Vec d => cexp (-((PDE.vecDot ξ z : ℝ) * I)) := by
  unfold PDE.vecDot
  fun_prop

/-- The character `e^{-i ξ·z}` has modulus one. -/
lemma norm_exp_vecDot (ξ z : PDE.Vec d) : ‖cexp (-((PDE.vecDot ξ z : ℝ) * I))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The fibre Fourier transform is jointly measurable in `(ξ, y)`. -/
lemma measurable_fiberFourier (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ] :
    Measurable fun p : PDE.Vec d × Y => fiberFourier κ p.1 p.2 := by
  have hc : Continuous fun q : PDE.Vec d × PDE.Vec d =>
      cexp (-((PDE.vecDot q.1 q.2 : ℝ) * I)) := by
    unfold PDE.vecDot
    fun_prop
  have hf : Measurable fun q : (PDE.Vec d × Y) × PDE.Vec d =>
      cexp (-((PDE.vecDot q.1.1 q.2 : ℝ) * I)) :=
    hc.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have := (hf.stronglyMeasurable).integral_kernel_prod_right'
    (κ := Kernel.prodMkLeft (PDE.Vec d) κ)
  exact this.measurable

/-- The fibre Fourier transform is continuous in `ξ` for fixed `y`. -/
lemma continuous_fiberFourier (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (y : Y) :
    Continuous fun ξ => fiberFourier κ ξ y := by
  unfold fiberFourier
  refine continuous_of_dominated (bound := fun _ => 1) (fun ξ => ?_)
    (fun ξ => Filter.Eventually.of_forall fun z => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun z => continuous_exp_vecDot z)
  · exact (Continuous.aestronglyMeasurable (by unfold PDE.vecDot; fun_prop))
  · exact (norm_exp_vecDot ξ z).le

/-- The fibre Fourier transform of a probability kernel is bounded by one. -/
lemma norm_fiberFourier_le (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (ξ : PDE.Vec d)
    (y : Y) : ‖fiberFourier κ ξ y‖ ≤ 1 := by
  unfold fiberFourier
  refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall fun z =>
    (norm_exp_vecDot ξ z).le)).trans ?_
  simp

/-- The fibre representatives are jointly measurable in `(ξ, y)`. -/
lemma measurable_fiberDensity {g : Y → ℝ≥0∞} (hg : Measurable g) (κ : Kernel Y (PDE.Vec d))
    [IsSFiniteKernel κ] :
    Measurable fun p : PDE.Vec d × Y => fiberDensity g κ p.1 p.2 :=
  (Complex.measurable_ofReal.comp (hg.comp measurable_snd).ennreal_toReal).mul
    (measurable_fiberFourier κ)

/-- The fibre representative is measurable in `y` for fixed `ξ`. -/
lemma measurable_fiberDensity_right {g : Y → ℝ≥0∞} (hg : Measurable g)
    (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ] (ξ : PDE.Vec d) :
    Measurable (fiberDensity g κ ξ) :=
  (measurable_fiberDensity hg κ).comp measurable_prodMk_left


/-- The fibre height is measurable. -/
lemma measurable_fiberHeight {g : Y → ℝ≥0∞} (hg : Measurable g) (κ : Kernel Y (PDE.Vec d))
    [IsSFiniteKernel κ] : Measurable (fiberHeight g κ) := by
  unfold fiberHeight
  refine Measurable.const_mul ?_ _
  have : Measurable fun q : Y × PDE.Vec d => ‖fiberDensity g κ q.2 q.1‖ₑ :=
    ((measurable_fiberDensity hg κ).comp measurable_swap).enorm
  exact this.lintegral_prod_right'

/-- The Fourier marginal of `(m.withDensity g) ⊗ₘ κ` over `E × ℝ^d` is the integral of the
representative `k̃^ξ` over `E`. -/
lemma setIntegral_fiberDensity {m : Measure Y} {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hgtop : ∀ᵐ y ∂m, g y < ∞) (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ]
    [IsFiniteMeasure ((m.withDensity g) ⊗ₘ κ)] [SFinite m] (ξ : PDE.Vec d) {E : Set Y}
    (hE : MeasurableSet E) :
    ∫ y in E, fiberDensity g κ ξ y ∂m =
      ∫ p in E ×ˢ (univ : Set (PDE.Vec d)), cexp (-((PDE.vecDot ξ p.2 : ℝ) * I))
        ∂((m.withDensity g) ⊗ₘ κ) := by
  have hf : Measurable fun p : Y × PDE.Vec d => cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) := by
    have hc : Continuous fun z : PDE.Vec d => cexp (-((PDE.vecDot ξ z : ℝ) * I)) := by
      unfold PDE.vecDot
      fun_prop
    exact hc.measurable.comp measurable_snd
  have hint : IntegrableOn (fun p : Y × PDE.Vec d => cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)))
      (E ×ˢ (univ : Set (PDE.Vec d))) ((m.withDensity g) ⊗ₘ κ) :=
    (Integrable.of_bound hf.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => (norm_exp_vecDot ξ p.2).le)).integrableOn
  rw [Measure.setIntegral_compProd hE MeasurableSet.univ hint]
  simp only [Measure.restrict_univ]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hg
    (ae_restrict_of_ae hgtop) _ hE]
  refine setIntegral_congr_fun hE fun y _ => ?_
  simp only [fiberDensity, fiberFourier, Complex.real_smul]

/-- The density `g` of the marginal of a finite measure has finite integral. -/
lemma lintegral_ne_top_of_fst_eq {m : Measure Y} {g : Y → ℝ≥0∞}
    (Γ : Measure (Y × PDE.Vec d)) [IsFiniteMeasure Γ] (hΓ : Γ.fst = m.withDensity g) :
    ∫⁻ y, g y ∂m ≠ ∞ := by
  have h : (m.withDensity g) univ = Γ.fst univ := by rw [hΓ]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [h]
  exact measure_ne_top _ _

/-- The fibre representatives are integrable. -/
lemma integrable_fiberDensity {m : Measure Y} {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hg1 : ∫⁻ y, g y ∂m ≠ ∞) (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (ξ : PDE.Vec d) :
    Integrable (fiberDensity g κ ξ) m  := by
  have norm_fiberDensity_le (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (ξ : PDE.Vec d) (y : Y) :
      ‖fiberDensity g κ ξ y‖ ≤ (g y).toReal := by
    unfold fiberDensity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (norm_fiberFourier_le κ ξ y)
  exact (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hg1).mono'
    (measurable_fiberDensity_right hg κ ξ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_of_nonneg ENNReal.toReal_nonneg] using norm_fiberDensity_le κ ξ y)

/-- **Step Lemma 5.2.**  Let `Γ` be a finite measure on
`Y × ℝ^d` with `Y`-marginal `g dm`, and suppose that for each `ξ` the measure
`E ↦ ∫_{E × ℝ^d} e^{-i ξ·z} dΓ` has density `k ξ` with respect to `m`.  Then
`Γ = (g dm) ⊗ π` for the probability kernel `π = Γ.condKernel`; the representatives
`k̃^ξ(y) = g(y) ∫ e^{-i ξ·z} π_y(dz)` are jointly measurable in `(ξ, y)`, continuous in `ξ`, and
for each `ξ` equal `k ξ` `m`-almost everywhere, so every `L^p` norm of `k ξ` and the integral of
the `L^γ` norms are unchanged; the height `H` is measurable. -/
theorem fiber_disintegration {m : Measure Y} [SigmaFinite m] (Γ : Measure (Y × PDE.Vec d))
    [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g) (hΓ : Γ.fst = m.withDensity g)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ) :
    Γ = (m.withDensity g) ⊗ₘ Γ.condKernel ∧
    (∀ y, IsProbabilityMeasure (Γ.condKernel y)) ∧
    Measurable (fun p : PDE.Vec d × Y => fiberDensity g Γ.condKernel p.1 p.2) ∧
    (∀ y, Continuous fun ξ => fiberDensity g Γ.condKernel ξ y) ∧
    (∀ ξ, fiberDensity g Γ.condKernel ξ =ᵐ[m] k ξ) ∧
    (∀ ξ (p : ℝ≥0∞), eLpNorm (fiberDensity g Γ.condKernel ξ) p m = eLpNorm (k ξ) p m) ∧
    (∀ p : ℝ≥0∞, ∫⁻ ξ, eLpNorm (fiberDensity g Γ.condKernel ξ) p m =
      ∫⁻ ξ, eLpNorm (k ξ) p m) ∧
    Measurable (fiberHeight g Γ.condKernel) := by
  have hdis : Γ = (m.withDensity g) ⊗ₘ Γ.condKernel := by
    rw [← hΓ]; exact (Measure.disintegrate Γ Γ.condKernel).symm
  have hg1 := lintegral_ne_top_of_fst_eq Γ hΓ
  have hae : ∀ ξ, fiberDensity g Γ.condKernel ξ =ᵐ[m] k ξ := by
    intro ξ
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s _ _ => (integrable_fiberDensity hg hg1 _ ξ).integrableOn)
      (fun s _ _ => (hk ξ).1.integrableOn) fun s hs _ => ?_
    have : IsFiniteMeasure ((m.withDensity g) ⊗ₘ Γ.condKernel) := by rw [← hdis]; infer_instance
    rw [setIntegral_fiberDensity hg (ae_lt_top hg hg1) _ ξ hs, (hk ξ).2 s hs, ← hdis]
  refine ⟨hdis, fun y => inferInstance, measurable_fiberDensity hg _,
    fun y => continuous_const.mul (continuous_fiberFourier _ y), hae,
    fun ξ p => eLpNorm_congr_ae (hae ξ), fun p => ?_, measurable_fiberHeight hg _⟩
  exact lintegral_congr fun ξ => eLpNorm_congr_ae (hae ξ)

end
section
open MeasureTheory Filter Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : Measure α} {ν : Measure β}

/-- Minkowski's inequality when the left-hand side is finite (duality argument). -/
lemma minkowski_aux [SFinite m] [SFinite ν] {p : ℝ} (hp : 1 < p) {F : α → β → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hA : ∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m ≠ ∞) :
    (∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m) ^ (1 / p) ≤
      ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν := by
  set I : α → ℝ≥0∞ := fun y => ∫⁻ ξ, F y ξ ∂ν with hI
  have hIm : Measurable I := hF.lintegral_prod_right'
  set A := ∫⁻ y, I y ^ p ∂m with hAdef
  set B := ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν with hBdef
  have hq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hqdef
  have hp0 : 0 < p := by linarith
  have hq0 := hq.symm.pos
  have hpq : 1 / p + 1 / q = 1 := by simpa using hq.inv_add_inv_eq_one
  have hq1 : p - 1 = p / q := by
    have := hq.inv_add_inv_eq_one
    field_simp at this ⊢
    linarith
  have hIpow : Measurable fun y => I y ^ (p - 1) := hIm.pow_const _
  have hpq' : (p - 1) * q = p := by rw [hq1]; field_simp
  have hFy : ∀ y, Measurable (F y) := fun y => hF.comp measurable_prodMk_left
  have hFξ : ∀ ξ, Measurable fun y => F y ξ := fun ξ => hF.comp measurable_prodMk_right
  have hNm : Measurable fun ξ => (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) := by
    have : Measurable fun z : β × α => F z.2 z.1 ^ p := (hF.comp measurable_swap).pow_const p
    exact (this.lintegral_prod_right').pow_const _
  have key : A ≤ A ^ (1 / q) * B := by
    calc A = ∫⁻ y, I y ^ (p - 1) * I y ∂m := by
          refine lintegral_congr fun y => ?_
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith), ENNReal.rpow_one]
      _ = ∫⁻ y, ∫⁻ ξ, I y ^ (p - 1) * F y ξ ∂ν ∂m := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_const_mul _ (hFy y)]
      _ = ∫⁻ ξ, ∫⁻ y, I y ^ (p - 1) * F y ξ ∂m ∂ν := by
          refine lintegral_lintegral_swap ?_
          exact ((hIpow.comp measurable_fst).mul hF).aemeasurable
      _ ≤ ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) * (A ^ (1 / q)) ∂ν := by
          refine lintegral_mono fun ξ => ?_
          have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m hq (hFξ ξ).aemeasurable
            hIpow.aemeasurable
          have h2 : ∫⁻ y, (I y ^ (p - 1)) ^ q ∂m = A := by
            refine lintegral_congr fun y => ?_
            rw [← ENNReal.rpow_mul, hpq']
          simp only [Pi.mul_apply, h2] at h
          calc ∫⁻ y, I y ^ (p - 1) * F y ξ ∂m
              = ∫⁻ y, F y ξ * I y ^ (p - 1) ∂m := lintegral_congr fun y => mul_comm _ _
            _ ≤ _ := h
      _ = A ^ (1 / q) * B := by
          rw [lintegral_mul_const _ hNm, mul_comm]
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  · have hq' : 0 < 1 / q := by positivity
    have hsplit : A = A ^ (1 / q) * A ^ (1 / p) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hq'.le (by positivity), add_comm, hpq,
        ENNReal.rpow_one]
    have hne0 : A ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA).ne'
    rw [← ENNReal.mul_le_mul_iff_right hne0 (ENNReal.rpow_ne_top_of_nonneg hq'.le hA)]
    calc A ^ (1 / q) * A ^ (1 / p) = A := hsplit.symm
      _ ≤ _ := key


/-- Truncation of a jointly measurable function to finite-measure boxes and bounded values. -/
noncomputable def trunc (m : Measure α) (ν : Measure β) [SigmaFinite m] [SigmaFinite ν]
    (F : α → β → ℝ≥0∞) (n : ℕ) (y : α) (ξ : β) : ℝ≥0∞ :=
  (spanningSets m n ×ˢ spanningSets ν n).indicator (fun q => min (F q.1 q.2) n) (y, ξ)

section Trunc

variable [SigmaFinite m] [SigmaFinite ν] {F : α → β → ℝ≥0∞}

/-- The truncation is jointly measurable. -/
lemma measurable_trunc (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (Function.uncurry (trunc m ν F n)) := by
  unfold trunc
  exact (hF.min measurable_const).indicator
    ((measurableSet_spanningSets m n).prod (measurableSet_spanningSets ν n))

/-- The truncation is dominated by `F`. -/
lemma trunc_le (n : ℕ) (y : α) (ξ : β) : trunc m ν F n y ξ ≤ F y ξ := by
  unfold trunc
  by_cases h : (y, ξ) ∈ spanningSets m n ×ˢ spanningSets ν n
  · rw [Set.indicator_of_mem h]; exact min_le_left _ _
  · rw [Set.indicator_of_notMem h]; exact zero_le

/-- The truncation is monotone in `n`. -/
lemma trunc_mono (y : α) (ξ : β) : Monotone fun n => trunc m ν F n y ξ := by
  intro a b hab
  show trunc m ν F a y ξ ≤ trunc m ν F b y ξ
  unfold trunc
  by_cases h : (y, ξ) ∈ spanningSets m a ×ˢ spanningSets ν a
  · have h2 : (y, ξ) ∈ spanningSets m b ×ˢ spanningSets ν b :=
      ⟨spanningSets_mono hab h.1, spanningSets_mono hab h.2⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h2]
    exact min_le_min le_rfl (by exact_mod_cast hab)
  · rw [Set.indicator_of_notMem h]; exact zero_le

/-- The truncations increase to `F`. -/
lemma iSup_trunc (y : α) (ξ : β) : ⨆ n, trunc m ν F n y ξ = F y ξ := by
  refine le_antisymm (iSup_le fun n => trunc_le n y ξ) ?_
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨N, hN⟩ := mem_iUnion.1 (by rw [iUnion_spanningSets]; trivial : y ∈ ⋃ n, spanningSets m n)
  obtain ⟨N', hN'⟩ := mem_iUnion.1 (by rw [iUnion_spanningSets]; trivial :
    ξ ∈ ⋃ n, spanningSets ν n)
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (hc.trans_le le_top).ne
  have hmem : (y, ξ) ∈ spanningSets m (max (max N N') k) ×ˢ spanningSets ν (max (max N N') k) :=
    ⟨spanningSets_mono (le_trans (le_max_left _ _) (le_max_left _ _)) hN,
      spanningSets_mono (le_trans (le_max_right _ _) (le_max_left _ _)) hN'⟩
  refine lt_of_lt_of_le ?_ (le_iSup _ (max (max N N') k))
  unfold trunc
  rw [Set.indicator_of_mem hmem]
  exact lt_min hc (hk.trans_le (by exact_mod_cast le_max_right _ _))

/-- The truncated Minkowski left-hand side is finite. -/
lemma lintegral_trunc_ne_top {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∫⁻ y, (∫⁻ ξ, trunc m ν F n y ξ ∂ν) ^ p ∂m ≠ ∞ := by
  set c : ℝ≥0∞ := n * ν (spanningSets ν n) with hc
  have hI : ∀ y, ∫⁻ ξ, trunc m ν F n y ξ ∂ν ≤ (spanningSets m n).indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ spanningSets m n
    · rw [Set.indicator_of_mem hy]
      calc ∫⁻ ξ, trunc m ν F n y ξ ∂ν
          ≤ ∫⁻ ξ, (spanningSets ν n).indicator (fun _ => (n : ℝ≥0∞)) ξ ∂ν := by
            refine lintegral_mono fun ξ => ?_
            unfold trunc
            by_cases hξ : ξ ∈ spanningSets ν n
            · rw [Set.indicator_of_mem (show (y, ξ) ∈ spanningSets m n ×ˢ spanningSets ν n from
                ⟨hy, hξ⟩), Set.indicator_of_mem hξ]
              exact min_le_right _ _
            · rw [Set.indicator_of_notMem (fun h => hξ h.2)]; exact zero_le
        _ = c := by
            rw [lintegral_indicator_const (measurableSet_spanningSets ν n), hc]
    · rw [Set.indicator_of_notMem hy]
      have : ∀ ξ, trunc m ν F n y ξ = 0 := fun ξ => by
        unfold trunc
        exact Set.indicator_of_notMem (fun h => hy h.1) _
      simp [this]
  refine ne_top_of_le_ne_top (b := ∫⁻ y, (spanningSets m n).indicator (fun _ => c ^ p) y ∂m) ?_ ?_
  · rw [lintegral_indicator_const (measurableSet_spanningSets m n)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le (ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_spanningSets_lt_top ν n).ne))
      (measure_spanningSets_lt_top m n).ne
  · refine lintegral_mono fun y => ?_
    refine (ENNReal.rpow_le_rpow (hI y) hp.le).trans ?_
    by_cases hy : y ∈ spanningSets m n
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hp]

end Trunc


/-- Minkowski's integral inequality for nonnegative jointly measurable functions. -/
theorem minkowski_integral [SigmaFinite m] [SigmaFinite ν] {p : ℝ} (hp : 1 < p)
    {F : α → β → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    (∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m) ^ (1 / p) ≤
      ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν := by
  have hp0 : 0 < p := by linarith
  set B := ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν with hB
  have hGm := measurable_trunc (m := m) (ν := ν) hF
  have hn : ∀ n, ∫⁻ y, (∫⁻ ξ, trunc m ν F n y ξ ∂ν) ^ p ∂m ≤ B ^ p := by
    intro n
    have h2 : ∫⁻ ξ, (∫⁻ y, trunc m ν F n y ξ ^ p ∂m) ^ (1 / p) ∂ν ≤ B := by
      refine lintegral_mono fun ξ => ?_
      refine ENNReal.rpow_le_rpow (lintegral_mono fun y => ?_) (by positivity)
      exact ENNReal.rpow_le_rpow (trunc_le n y ξ) hp0.le
    have h3 := ENNReal.rpow_le_rpow ((minkowski_aux (m := m) (ν := ν) hp (hGm n) (lintegral_trunc_ne_top hp0 n)).trans h2) hp0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at h3
  have hI : ∀ y, ⨆ n, ∫⁻ ξ, trunc m ν F n y ξ ∂ν = ∫⁻ ξ, F y ξ ∂ν := by
    intro y
    have hmeas : ∀ n, Measurable fun ξ => trunc m ν F n y ξ :=
      fun n => (hGm n).comp measurable_prodMk_left
    have := lintegral_iSup (μ := ν) hmeas (fun a b hab ξ => trunc_mono y ξ hab)
    rw [← this]
    exact lintegral_congr fun ξ => iSup_trunc y ξ
  have hA : ∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m =
      ⨆ n, ∫⁻ y, (∫⁻ ξ, trunc m ν F n y ξ ∂ν) ^ p ∂m := by
    have hmono : ∀ y, Monotone fun n => ∫⁻ ξ, trunc m ν F n y ξ ∂ν :=
      fun y a b hab => lintegral_mono fun ξ => trunc_mono y ξ hab
    rw [← lintegral_iSup]
    · refine lintegral_congr fun y => ?_
      rw [← hI y]
      exact (ENNReal.monotone_rpow_of_nonneg hp0.le).map_iSup_of_continuousAt
        (ENNReal.continuous_rpow_const.continuousAt) (ENNReal.zero_rpow_of_pos hp0)
    · intro n
      exact ((hGm n).lintegral_prod_right').pow_const _
    · intro a b hab y
      exact ENNReal.rpow_le_rpow (lintegral_mono fun ξ => trunc_mono y ξ hab) hp0.le
  have hAB : ∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m ≤ B ^ p := by
    rw [hA]; exact iSup_le hn
  have := ENNReal.rpow_le_rpow hAB (show 0 ≤ 1 / p by positivity)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at this

end
section
open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The `L^γ(m)` norm of the fibre height is the Minkowski integral of the `L^γ` norms of the
Fourier representatives, for any measurable `g` and Markov kernel `κ`. -/
lemma eLpNorm_fiberHeight_le {m : Measure Y} [SigmaFinite m] {g : Y → ℝ≥0∞}
    (hg : Measurable g) (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] {γ : ℝ} (hγ : 1 < γ) :
    eLpNorm (fiberHeight g κ) (ENNReal.ofReal γ) m ≤
      ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ∫⁻ ξ, eLpNorm (fiberDensity g κ ξ) (ENNReal.ofReal γ) m := by
  have hγ0 : 0 < γ := by linarith
  have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ0
  have hpT : ENNReal.ofReal γ ≠ ∞ := ENNReal.ofReal_ne_top
  set c : ℝ≥0∞ := ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) with hc
  set F : Y → PDE.Vec d → ℝ≥0∞ := fun y ξ => ‖fiberDensity g κ ξ y‖ₑ with hF
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_fiberDensity hg κ).comp measurable_swap).enorm
  have hHm := measurable_fiberHeight hg κ
  have hnorm : ∀ ξ, eLpNorm (fiberDensity g κ ξ) (ENNReal.ofReal γ) m =
      (∫⁻ y, F y ξ ^ γ ∂m) ^ (1 / γ) := by
    intro ξ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT
      (measurable_fiberDensity_right hg κ ξ).aestronglyMeasurable, ENNReal.toReal_ofReal hγ0.le]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT hHm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hγ0.le]
  simp_rw [hnorm]
  have h1 : ∫⁻ y, ‖fiberHeight g κ y‖ₑ ^ γ ∂m =
      c ^ γ * ∫⁻ y, (∫⁻ ξ, F y ξ) ^ γ ∂m := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hγ0.le
      ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun y => ?_
    rw [enorm_eq_self, fiberHeight, ENNReal.mul_rpow_of_nonneg _ _ hγ0.le]
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hγ0.ne', ENNReal.rpow_one]
  exact mul_le_mul_right (minkowski_integral (m := m) (ν := (volume : Measure (PDE.Vec d))) hγ hFm) c


/-- A function in `L^γ` with `γ > 0` is finite almost everywhere. -/
lemma ae_lt_top_of_eLpNorm_lt_top {m : Measure Y} {H : Y → ℝ≥0∞} (hH : Measurable H) {γ : ℝ}
    (hγ : 0 < γ) (h : eLpNorm H (ENNReal.ofReal γ) m < ∞) : ∀ᵐ y ∂m, H y < ∞ := by
  have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top
    hH.aestronglyMeasurable, ENNReal.toReal_ofReal hγ.le] at h
  have h2 := ae_lt_top (hH.enorm.pow_const γ) h.ne
  filter_upwards [h2] with y hy
  rw [enorm_eq_self] at hy
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.top_rpow_of_pos hγ] at hy
  exact lt_irrefl _ hy

/-- **Step Lemma 5.2.**  Under the hypotheses of
`fiber_disintegration`, Minkowski's integral inequality gives
`‖H‖_{L^γ(m)} ≤ 𝖧 = (2π)^{-d} ∫ ‖k ξ‖_{L^γ(m)} dξ`.  If `𝖧 < ∞` then `H(y) < ∞` and
`ξ ↦ k̃^ξ(y)` is integrable for `m`-almost every `y`. -/
theorem fiber_height_minkowski {m : Measure Y} [SigmaFinite m] (Γ : Measure (Y × PDE.Vec d))
    [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g) (hΓ : Γ.fst = m.withDensity g)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    {γ : ℝ} (hγ : 1 < γ) :
    eLpNorm (fiberHeight g Γ.condKernel) (ENNReal.ofReal γ) m ≤
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m ∧
      (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞ →
        ∀ᵐ y ∂m, fiberHeight g Γ.condKernel y < ∞ ∧
          Integrable (fun ξ => fiberDensity g Γ.condKernel ξ y)) := by
  obtain ⟨-, -, -, -, -, -, hnorm, hHm⟩ := fiber_disintegration Γ hg hΓ k hk
  have hle := eLpNorm_fiberHeight_le (m := m) hg Γ.condKernel hγ
  rw [hnorm (ENNReal.ofReal γ)] at hle
  refine ⟨hle, fun hfin => ?_⟩
  have hlt : eLpNorm (fiberHeight g Γ.condKernel) (ENNReal.ofReal γ) m < ∞ :=
    lt_of_le_of_lt hle hfin
  filter_upwards [ae_lt_top_of_eLpNorm_lt_top hHm (by linarith) hlt] with y hy
  refine ⟨hy, ⟨(continuous_const.mul (continuous_fiberFourier _ y)).aestronglyMeasurable, ?_⟩⟩
  have hc : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) ≠ 0 := by
    have := Real.pi_pos
    simpa using (by positivity : 0 < ((2 * Real.pi) ^ d)⁻¹)
  have : ∫⁻ ξ, ‖fiberDensity g Γ.condKernel ξ y‖ₑ < ∞ := by
    unfold fiberHeight at hy
    rcases ENNReal.mul_lt_top_iff.1 hy with ⟨_, h⟩ | h | h
    · exact h
    · exact absurd h hc
    · rw [h]; exact ENNReal.zero_lt_top
  exact this

end
section
open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The fibre density `G(y, z) = (2π)^{-d} Re ∫ e^{i ξ·z} k̃^ξ(y) dξ` obtained by Fourier
inversion. -/
def fiberInversionDensity (g : Y → ℝ≥0∞) (κ : Kernel Y (PDE.Vec d)) (p : Y × PDE.Vec d) :
    ℝ≥0∞ :=
  ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹ *
    (vecInvIntegral (fun ξ => fiberDensity g κ ξ p.1) p.2).re)

/-- The Fourier transform of `g(y) • κ y` is the fibre representative `k̃^ξ(y)`. -/
lemma vecFourier_smul_kernel (κ : Kernel Y (PDE.Vec d)) (g : Y → ℝ≥0∞) (y : Y)
    (ξ : PDE.Vec d) : vecFourier ((g y) • κ y) ξ = fiberDensity g κ ξ y := by
  unfold vecFourier fiberDensity fiberFourier
  rw [integral_smul_measure, Complex.real_smul]

/-- Fibre inversion at a single `y`: the measure `g(y) π_y` equals the Lebesgue measure with
density `G(y, ·)`, and `G(y, ·) ≤ H(y)`. -/
lemma fiber_inversion_at (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] (g : Y → ℝ≥0∞) (y : Y)
    (hy : g y < ∞) (hint : Integrable (fun ξ => fiberDensity g κ ξ y)) :
    (volume : Measure (PDE.Vec d)).withDensity (fun z => fiberInversionDensity g κ (y, z)) =
        (g y) • κ y ∧
      ∀ z, fiberInversionDensity g κ (y, z) ≤ fiberHeight g κ y := by
  have : IsFiniteMeasure ((g y) • κ y) :=
    ⟨by simp [Measure.smul_apply, hy]⟩
  have hfun : vecFourier ((g y) • κ y) = fun ξ => fiberDensity g κ ξ y :=
    funext (vecFourier_smul_kernel κ g y)
  have hφ : Integrable (vecFourier ((g y) • κ y)) := by rw [hfun]; exact hint
  have hG : ∀ z, fiberInversionDensity g κ (y, z) =
      ENNReal.ofReal (vecInvDensity ((g y) • κ y) z) := by
    intro z
    simp only [fiberInversionDensity, vecInvDensity, hfun]
  refine ⟨?_, fun z => ?_⟩
  · calc (volume : Measure (PDE.Vec d)).withDensity (fun z => fiberInversionDensity g κ (y, z))
        = (volume : Measure (PDE.Vec d)).withDensity
            (fun z => ENNReal.ofReal (vecInvDensity ((g y) • κ y) z)) := by
          simp only [hG]
      _ = (g y) • κ y := (eq_withDensity_vecInvDensity ((g y) • κ y) hφ).symm
  · rw [hG]
    have hle := vecInvDensity_le ((g y) • κ y) hφ z
    refine (ENNReal.ofReal_le_ofReal hle).trans (le_of_eq ?_)
    rw [fiberHeight, ENNReal.ofReal_mul (by positivity), hfun]
    congr 1
    rw [ofReal_integral_norm_eq_lintegral_enorm hint]




/-- Pointwise `L^q` bound on a fibre from `G ≤ H` and `∫ G = g`. -/
lemma lintegral_rpow_le_of_le {μ : Measure (PDE.Vec d)} {G : PDE.Vec d → ℝ≥0∞} {H a : ℝ≥0∞}
    {q : ℝ} (hq : 1 < q) (hHT : H ≠ ∞) (hG : ∀ z, G z ≤ H) (hint : ∫⁻ z, G z ∂μ = a) :
    ∫⁻ z, G z ^ q ∂μ ≤ H ^ (q - 1) * a := by
  calc ∫⁻ z, G z ^ q ∂μ ≤ ∫⁻ z, H ^ (q - 1) * G z ∂μ := by
        refine lintegral_mono fun z => ?_
        calc G z ^ q = G z ^ (q - 1) * G z := by
              conv_lhs => rw [show q = (q - 1) + 1 by ring]
              rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith), ENNReal.rpow_one]
          _ ≤ H ^ (q - 1) * G z :=
              mul_le_mul_left (ENNReal.rpow_le_rpow (hG z) (by linarith)) _
    _ = H ^ (q - 1) * a := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hHT), hint]


/-- **Step Lemma 5.2.**  Under the hypotheses of the reconstruction
lemma, the fibre inversion density `G` is jointly measurable, `Γ` has density `G` with respect to
`m ⊗ Leb`, and for `m`-almost every `y` one has `G(y, ·) ≤ H(y)`, `∫ G(y, z) dz = g(y)` and
`∫ G(y, z)^q dz ≤ H(y)^{q-1} g(y)`. -/
theorem fiber_inversion {m : Measure Y} [SigmaFinite m] (Γ : Measure (Y × PDE.Vec d))
    [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g) (hΓ : Γ.fst = m.withDensity g)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    {γ q : ℝ} (hγ : 1 < γ) (hq : 1 < q)
    (hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞) :
    Measurable (fiberInversionDensity g Γ.condKernel) ∧
      Γ = (m.prod volume).withDensity (fiberInversionDensity g Γ.condKernel) ∧
      ∀ᵐ y ∂m, (∀ z, fiberInversionDensity g Γ.condKernel (y, z) ≤ fiberHeight g Γ.condKernel y) ∧
        ∫⁻ z, fiberInversionDensity g Γ.condKernel (y, z) = g y ∧
        ∫⁻ z, fiberInversionDensity g Γ.condKernel (y, z) ^ q ≤
          fiberHeight g Γ.condKernel y ^ (q - 1) * g y  := by
  have measurable_fiberInversionDensity (κ : Kernel Y (PDE.Vec d)) [IsSFiniteKernel κ] :
      Measurable (fiberInversionDensity g κ) := by
    unfold fiberInversionDensity
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Complex.measurable_re.comp ?_))
    have hc : Continuous fun q : PDE.Vec d × PDE.Vec d =>
        cexp (I * ((PDE.vecDot q.1 q.2 : ℝ) : ℂ)) := by
      unfold PDE.vecDot
      fun_prop
    have hf : Measurable fun q : (Y × PDE.Vec d) × PDE.Vec d =>
        cexp (I * ((PDE.vecDot q.2 q.1.2 : ℝ) : ℂ)) * fiberDensity g κ q.2 q.1.1 :=
      (hc.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
        ((measurable_fiberDensity hg κ).comp (measurable_snd.prodMk
          (measurable_fst.comp measurable_fst)))
    exact (StronglyMeasurable.integral_prod_right (f := fun (p : Y × PDE.Vec d) (ξ : PDE.Vec d) =>
      cexp (I * ((PDE.vecDot ξ p.2 : ℝ) : ℂ)) * fiberDensity g κ ξ p.1)
      hf.stronglyMeasurable).measurable
  obtain ⟨hdis, -⟩ := fiber_disintegration Γ hg hΓ k hk
  have hfin := (fiber_height_minkowski Γ hg hΓ k hk hγ).2 hH
  have hgtop : ∀ᵐ y ∂m, g y < ∞ := ae_lt_top hg (lintegral_ne_top_of_fst_eq Γ hΓ)
  set κ := Γ.condKernel with hκ
  have hGm := measurable_fiberInversionDensity κ
  have hfib : ∀ᵐ y ∂m, (volume : Measure (PDE.Vec d)).withDensity
        (fun z => fiberInversionDensity g κ (y, z)) = (g y) • κ y ∧
      ∀ z, fiberInversionDensity g κ (y, z) ≤ fiberHeight g κ y ∧ fiberHeight g κ y < ∞ := by
    filter_upwards [hgtop, hfin] with y hy hy2
    obtain ⟨h1, h2⟩ := fiber_inversion_at κ g y hy hy2.2
    exact ⟨h1, fun z => ⟨h2 z, hy2.1⟩⟩
  refine ⟨hGm, ?_, ?_⟩
  · ext S hS
    have hS' : ∀ y, MeasurableSet (Prod.mk y ⁻¹' S) := fun y => measurable_prodMk_left hS
    have hL : Γ S = ∫⁻ y, g y * κ y (Prod.mk y ⁻¹' S) ∂m := by
      have h := congrArg (fun μ : Measure (Y × PDE.Vec d) => μ S) hdis
      rw [h, Measure.compProd_apply hS,
        lintegral_withDensity_eq_lintegral_mul _ hg (Kernel.measurable_kernel_prodMk_left hS)]
      rfl
    have hR : ((m.prod volume).withDensity (fiberInversionDensity g κ)) S =
        ∫⁻ y, ∫⁻ z in Prod.mk y ⁻¹' S, fiberInversionDensity g κ (y, z) ∂volume ∂m := by
      rw [withDensity_apply _ hS, ← lintegral_indicator hS,
        lintegral_prod _ ((hGm.indicator hS).aemeasurable)]
      refine lintegral_congr fun y => ?_
      rw [← lintegral_indicator (hS' y)]
      refine lintegral_congr fun z => ?_
      by_cases h : (y, z) ∈ S <;> simp [Set.indicator, h]
    rw [hL, hR]
    refine lintegral_congr_ae ?_
    filter_upwards [hfib] with y ⟨h1, _⟩
    have := congrArg (fun μ : Measure (PDE.Vec d) => μ (Prod.mk y ⁻¹' S)) h1
    simp [withDensity_apply _ (hS' y), Measure.smul_apply] at this
    exact this.symm
  · filter_upwards [hfib] with y ⟨h1, h2⟩
    have hint : ∫⁻ z, fiberInversionDensity g κ (y, z) = g y := by
      have := congrArg (fun μ => μ univ) h1
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at this
      exact this
    exact ⟨fun z => (h2 z).1, hint, lintegral_rpow_le_of_le hq (h2 0).2.ne (fun z => (h2 z).1) hint⟩

end
open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The final Hölder step: `∫ H^{q-1} g ≤ (∫ H^γ)^{(q-1)/γ} (∫ g^{q₁})^{1/q₁}`. -/
lemma lintegral_rpow_mul_le {m : Measure Y} {H g : Y → ℝ≥0∞} (hH : Measurable H)
    (hg : Measurable g) {q γ q₁ : ℝ} (hq : 1 < q) (hqγ : q < γ)
    (hq₁ : (q - 1) / γ + 1 / q₁ = 1) :
    ∫⁻ y, H y ^ (q - 1) * g y ∂m ≤
      (∫⁻ y, H y ^ γ ∂m) ^ ((q - 1) / γ) * (∫⁻ y, g y ^ q₁ ∂m) ^ (1 / q₁) := by
  have hq0 : 0 < q - 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  set P : ℝ := γ / (q - 1) with hP
  have hP1 : 1 < P := by rw [hP, lt_div_iff₀ hq0]; linarith
  have hPinv : P⁻¹ = (q - 1) / γ := by rw [hP, inv_div]
  have hconj : P.HolderConjugate q₁ :=
    Real.holderConjugate_iff.2 ⟨hP1, by rw [hPinv, one_div] at *; exact hq₁⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m hconj (hH.pow_const (q - 1)).aemeasurable
    hg.aemeasurable
  have h2 : ∫⁻ y, (H y ^ (q - 1)) ^ P ∂m = ∫⁻ y, H y ^ γ ∂m := by
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.rpow_mul, hP, mul_div_cancel₀ _ hq0.ne']
  simp only [Pi.mul_apply, h2] at h
  rwa [one_div, hPinv] at h


/-- Lemma Lemma 5.2 for a Borel-measurable density `g`. -/
theorem reconstruction_of_measurable {m : Measure Y} [SigmaFinite m]
    (Γ : Measure (Y × PDE.Vec d)) [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hΓ : Γ.fst = m.withDensity g) {q γ q₁ : ℝ} (hq : 1 < q) (hqγ : q < γ)
    (hq₁ : (q - 1) / γ + 1 / q₁ = 1) (hgL : eLpNorm g (ENNReal.ofReal q₁) m < ∞)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    (hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞) :
    ∃ G : Y × PDE.Vec d → ℝ≥0∞, Measurable G ∧ Γ = (m.prod volume).withDensity G ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) ≤
        (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m) ^ (q - 1) *
        eLpNorm g (ENNReal.ofReal q₁) m ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) < ∞ := by
  have hγ1 : 1 < γ := hq.trans hqγ
  have hγ0 : 0 < γ := by linarith
  have hq0 : 0 < q - 1 := by linarith
  have hq₁0 : 0 < q₁ := by
    by_contra hneg
    have h1 : 0 < (q - 1) / γ := by positivity
    have h2 : (q - 1) / γ < 1 := by rw [div_lt_one hγ0]; linarith
    have h3 : 1 / q₁ ≤ 0 := by rw [one_div]; exact inv_nonpos.2 (not_lt.1 hneg)
    linarith
  obtain ⟨hGm, hΓG, hfib⟩ := fiber_inversion Γ hg hΓ k hk hγ1 hq hH
  have hmink := (fiber_height_minkowski Γ hg hΓ k hk hγ1).1
  set κ := Γ.condKernel with hκ
  set H := fiberHeight g κ with hHdef
  have hHm : Measurable H := measurable_fiberHeight hg κ
  have hq1 : ∀ᵐ y ∂m, ∫⁻ z, fiberInversionDensity g κ (y, z) ^ q ≤ H y ^ (q - 1) * g y := by
    filter_upwards [hfib] with y hy using hy.2.2
  have hbound : ∫⁻ p, fiberInversionDensity g κ p ^ q ∂(m.prod volume) ≤
      (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m) ^ (q - 1) *
      eLpNorm g (ENNReal.ofReal q₁) m := by
   calc ∫⁻ p, fiberInversionDensity g κ p ^ q ∂(m.prod volume)
      = ∫⁻ y, ∫⁻ z, fiberInversionDensity g κ (y, z) ^ q ∂volume ∂m :=
        lintegral_prod _ (hGm.pow_const q).aemeasurable
    _ ≤ ∫⁻ y, H y ^ (q - 1) * g y ∂m := lintegral_mono_ae hq1
    _ ≤ (∫⁻ y, H y ^ γ ∂m) ^ ((q - 1) / γ) * (∫⁻ y, g y ^ q₁ ∂m) ^ (1 / q₁) :=
        lintegral_rpow_mul_le hHm hg hq hqγ hq₁
    _ ≤ _ := by
        have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ0
        have hp1 : ENNReal.ofReal q₁ ≠ 0 := by simpa using hq₁0
        have hHnorm : eLpNorm H (ENNReal.ofReal γ) m = (∫⁻ y, H y ^ γ ∂m) ^ (1 / γ) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
            hHm.aestronglyMeasurable, ENNReal.toReal_ofReal hγ0.le]
          simp only [enorm_eq_self]
        have hgnorm : eLpNorm g (ENNReal.ofReal q₁) m = (∫⁻ y, g y ^ q₁ ∂m) ^ (1 / q₁) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top
            hg.aestronglyMeasurable, ENNReal.toReal_ofReal hq₁0.le]
          simp only [enorm_eq_self]
        rw [← hgnorm]
        refine mul_le_mul' ?_ le_rfl
        have : (∫⁻ y, H y ^ γ ∂m) ^ ((q - 1) / γ) = eLpNorm H (ENNReal.ofReal γ) m ^ (q - 1) := by
          rw [hHnorm, ← ENNReal.rpow_mul]
          congr 1
          field_simp
        rw [this]
        exact ENNReal.rpow_le_rpow hmink hq0.le
  exact ⟨_, hGm, hΓG, hbound, lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le hH.ne) hgL)⟩


/-- **Lemma Lemma 5.2** (Reconstruction from the marginal and the Fourier bounds).

Let `m` be a σ-finite measure on `Y`, `Γ` a finite measure on `Y × ℝ^d` whose `Y`-marginal is
`g dm`, `1 < q < γ`, `(q-1)/γ + 1/q₁ = 1` and `g ∈ L^{q₁}(m)`.  Suppose that for every
`ξ ∈ ℝ^d` the complex measure `E ↦ ∫_{E × ℝ^d} e^{-i ξ·z} dΓ` has the density `k ξ ∈ L^1(m)` with
respect to `m`, and that `𝖧 = (2π)^{-d} ∫ ‖k ξ‖_{L^γ(m)} dξ < ∞`.  Then `Γ` has a measurable
density `G` with respect to `m ⊗ Leb`, and `‖G‖_{L^q}^q = ∫ G^q ≤ 𝖧^{q-1} ‖g‖_{L^{q₁}(m)} < ∞`.

The paper's `Y` (a Borel subset of a Euclidean space with its Borel `σ`-algebra) is the special
case `Y = ↥S` of an arbitrary measurable space.  Here `ℝ^d` is `PDE.Vec d = Fin d → ℝ` with
product Lebesgue measure and `ξ·z = PDE.vecDot ξ z`.
The hypothesis that each `k ξ` lies in `L^γ(m)` is not needed beyond `𝖧 < ∞`. -/
theorem reconstruction {m : Measure Y} [SigmaFinite m]
    (Γ : Measure (Y × PDE.Vec d)) [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hgm : AEMeasurable g m)
    (hΓ : Γ.fst = m.withDensity g) {q γ q₁ : ℝ} (hq : 1 < q) (hqγ : q < γ)
    (hq₁ : (q - 1) / γ + 1 / q₁ = 1) (hgL : eLpNorm g (ENNReal.ofReal q₁) m < ∞)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    (hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞) :
    ∃ G : Y × PDE.Vec d → ℝ≥0∞, Measurable G ∧ Γ = (m.prod volume).withDensity G ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) ≤
        (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m) ^ (q - 1) *
        eLpNorm g (ENNReal.ofReal q₁) m ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) < ∞ := by
  have hae : g =ᵐ[m] hgm.mk g := hgm.ae_eq_mk
  have hnorm : eLpNorm g (ENNReal.ofReal q₁) m = eLpNorm (hgm.mk g) (ENNReal.ofReal q₁) m :=
    eLpNorm_congr_ae hae
  rw [hnorm] at hgL ⊢
  exact reconstruction_of_measurable Γ hgm.measurable_mk
    (hΓ.trans (withDensity_congr_ae hae)) hq hqγ hq₁ hgL k hk hH

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

