/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosNegativePower
public import DOZZ.GMC.FiniteChaosMean
public import DOZZ.GMC.Moments.ChaosLawFDD
public import DOZZ.Statements.GMC.FieldChaosMass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Negative-power Kahane comparison for continuum Gaussian fields. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]


section
variable (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
include hΦ

/-- The pointwise variance of a jointly measurable centered Gaussian field is measurable in its
spatial variable. -/
theorem centeredGaussianField_variance_measurable

 :
    Measurable (fun x => DOZZ.gaussianVariance P (fun ω => Φ ω x)) := by
  have := (hΦ.2 0 Fin.elim0).1
  have hf : Measurable fun q : S × Ω => Φ q.2 q.1 := hΦ.1.comp measurable_swap
  exact (hf.mul hf).stronglyMeasurable.integral_prod_right.measurable

private theorem centeredGaussianField_covariance_measurable

 :
    Measurable (fun xy : S × S =>
      DOZZ.gaussianCovariance P (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2)) := by
  have := (hΦ.2 0 Fin.elim0).1
  have hf : Measurable fun q : (S × S) × Ω => Φ q.2 q.1.1 * Φ q.2 q.1.2 :=
    (hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.1))).mul
      (hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.2)))
  exact hf.stronglyMeasurable.integral_prod_right.measurable


end
/-- A bounded nonnegative measurable weight is integrable under the normalized version of a
finite reference measure. -/
theorem centeredGaussianField_bounded_weight_integrable
    {S : Type*} [MeasurableSpace S] [Nonempty S] (ν : FiniteMeasure S)
    (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) :
    Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) := by
  obtain ⟨c, hc⟩ := hhb
  refine (integrable_const (c : ℝ)).mono'
    (measurable_coe_nnreal_real.comp hh).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast hc x

/-- Almost every field section has an integrable weighted Wick density under a probability
reference measure. -/
theorem centeredGaussianField_ae_integrable_weighted_wick
 [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S) := by
  have := (hΦ.2 0 Fin.elim0).1
  have hlaw_nn (x : S) : HasLaw (fun ω => Φ ω x)
      (gaussianReal 0 (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal) P ∧
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    have hZ := hΦ.2 1 (fun _ => x)
    obtain ⟨v, hmap, _, hvar⟩ := DOZZ.Proofs.coordinate_mean_variance P _ hZ 0
    refine ⟨⟨hZ.2.1 0, ?_⟩, hvar ▸ NNReal.coe_nonneg v⟩
    rw [hvar, Real.toNNReal_coe]; exact hmap
  have hsec := ae_integrable_weighted_wick_sections (ν.normalize : Measure S) Φ
    (fun x => (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal)
    (fun x => (h x : ℝ)) γ hΦ.1
    (measurable_real_toNNReal.comp (centeredGaussianField_variance_measurable P Φ hΦ))
    (measurable_coe_nnreal_real.comp hh) (fun x => (hlaw_nn x).1)
    (fun x => NNReal.coe_nonneg (h x)) (centeredGaussianField_bounded_weight_integrable ν h hh hhb)
  filter_upwards [hsec] with ω hω
  exact hω.congr (ae_of_all _ fun x => by simp [Real.coe_toNNReal _ (hlaw_nn x).2])

/-- The finite-cutoff field chaos mass is measurable. -/
theorem centeredGaussianField_fieldChaosMass_measurable

    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) [SFinite ν] (h : S → ℝ≥0) (hh : Measurable h) (γ : ℝ) :
    Measurable (fun ω => DOZZ.fieldChaosMass P Φ ν h γ ω) := by
  have hvInt : Measurable fun x => ∫ ω, Φ ω x ^ 2 ∂P := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using
      centeredGaussianField_variance_measurable P Φ hΦ
  unfold DOZZ.fieldChaosMass
  exact ((measurable_coe_nnreal_ennreal.comp (hh.comp measurable_snd)).mul
    (ENNReal.continuous_ofReal.measurable.comp (Real.measurable_exp.comp
      ((measurable_const.mul hΦ.1).sub (measurable_const.mul (hvInt.comp measurable_snd)))))).lintegral_prod_right'

theorem ae_empirical_average_tendsto

    (P : Measure Ω) (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → S → ℝ)
    (hjoint : Measurable (fun p : Ω × S => f p.1 p.2))
    (hint : ∀ᵐ ω ∂P, Integrable (f ω) ν) :
    ∀ᵐ ω ∂P, ∀ᵐ q ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
  let Q := Measure.infinitePi (fun _ : ℕ => ν)
  have hEv (i : ℕ) : IdentDistrib (fun q : ℕ → S => q i) id Q ν :=
    ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id,
      by simpa [Q] using Measure.infinitePi_map_eval (fun _ : ℕ => ν) i⟩
  have hind : iIndepFun (fun i (q : ℕ → S) => q i) Q := by
    simpa [Q] using iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id) (by fun_prop)
  filter_upwards [hint] with ω hω
  have hfm : Measurable (f ω) := hjoint.comp (by fun_prop : Measurable fun x : S => (ω, x))
  have hs0 := (hEv 0).comp hfm
  have hm : (∫ q, f ω (q 0) ∂Q) = ∫ x, f ω x ∂ν := hs0.integral_eq
  have hlln := ProbabilityTheory.strong_law_ae (μ := Q) (fun i (q : ℕ → S) => f ω (q i))
    (hs0.integrable_iff.mpr hω)
    (fun i j hij => (hind.comp (fun _ => f ω) (fun _ => hfm)).indepFun hij)
    (fun i => ((hEv i).trans (hEv 0).symm).comp hfm)
  filter_upwards [hlln] with q hq
  simpa only [smul_eq_mul, ← Fin.sum_univ_eq_sum_range, hm] using hq

theorem fieldChaosMass_eq_ofReal_normalized_integral
 [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω)
    (hint : Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S)) :
    DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω =
      ENNReal.ofReal ((ν.mass : ℝ) * ∫ x, (h x : ℝ) *
        Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Φ ω x)) ∂(ν.normalize : Measure S)) := by
  let f : S → ℝ := fun x => (h x : ℝ) *
    Real.exp (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) :=
    congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  unfold DOZZ.fieldChaosMass
  rw [show (fun x => (h x : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) = fun x => ENNReal.ofReal (f x) by
    ext x
    simp only [f, DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]]
  rw [hνeq, lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)),
    ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]

theorem centeredGaussianField_covariance_order_samples
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∀ n, ∀ᵐ u ∂Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S)),
      ∀ i j : Fin n,
        DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i.val)) (fun ω => Φ ω (u j.val)) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i.val)) (fun ω => Ψ ω (u j.val)) := by
  have hρν : (ν.normalize : Measure S) ≪ (ν : Measure S) := by
    rw [congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize]
    exact Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν))
  let Q := Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S))
  intro n; rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
  by_cases hij : i.val = j.val
  · obtain rfl := Fin.ext hij
    refine (ae_map_iff (by fun_prop : Measurable fun u : ℕ → S => u i.val).aemeasurable
      (measurableSet_le (centeredGaussianField_variance_measurable PX Φ hΦ)
        (centeredGaussianField_variance_measurable PY Ψ hΨ))).1 ?_
    rw [Measure.infinitePi_map_eval (fun _ : ℕ => (ν.normalize : Measure S)) i.val]
    exact hρν.ae_le hdiag
  · refine (ae_map_iff (by fun_prop : Measurable fun u : ℕ → S => (u i.val, u j.val)).aemeasurable
      (measurableSet_le (centeredGaussianField_covariance_measurable PX Φ hΦ)
        (centeredGaussianField_covariance_measurable PY Ψ hΨ))).1 ?_
    rw [Measure.infinitePi_map_eval_prod (P := fun _ : ℕ => (ν.normalize : Measure S)) hij]
    exact (hρν.prod hρν).ae_le hcov

section
variable [Nonempty S] (P : Measure Ω) (Φ : Ω → S → ℝ)
include P Φ

private theorem tendsto_lintegral_finiteChaosMass_laplace
 (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun n : ℕ => ∫⁻ u, ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
        DOZZ.finiteChaosMass P (fun ω (i : Fin n) => Φ ω (u i.val))
          (fun i => (ν.mass : ℝ) * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂P
        ∂Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S)))
      atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
        (DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal)) ∂P)) := by
  have := (hΦ.2 0 Fin.elim0).1
  let ρ : Measure S := ν.normalize
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ : ℕ => ρ)
  let c : ℝ := ν.mass
  let w : Ω → S → ℝ := fun ω x => (h x : ℝ) *
    Real.exp (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hvar := centeredGaussianField_variance_measurable P Φ hΦ
  have hw : Measurable fun p : Ω × S => w p.1 p.2 :=
    ((measurable_coe_nnreal_real.comp hh).comp measurable_snd).mul
      (Real.measurable_exp.comp ((measurable_const.mul hΦ.1).sub
        (measurable_const.mul (hvar.comp measurable_snd))))
  have hint : ∀ᵐ ω ∂P, Integrable (w ω) ρ :=
    centeredGaussianField_ae_integrable_weighted_wick P Φ hΦ ν h hh hhb γ
  let lim : Ω → ℝ := fun ω => c * ∫ x, w ω x ∂ρ
  have hlim_meas : Measurable lim :=
    measurable_const.mul hw.stronglyMeasurable.integral_prod_right'.measurable
  let F : ℕ → Ω × (ℕ → S) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-s * (c * ((n : ℝ)⁻¹ * ∑ i : Fin n, w p.1 (p.2 i.val)))))
  have hFmeas (n : ℕ) : Measurable (F n) := by fun_prop
  let L : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-s * lim ω))
  have hLmeas : Measurable L := by fun_prop
  have hbd (n : ℕ) (p : Ω × (ℕ → S)) : F n p ≤ 1 := by
    have h0 : 0 ≤ c * ((n : ℝ)⁻¹ * ∑ i : Fin n, w p.1 (p.2 i.val)) :=
      mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun _ _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)))
    simpa [F] using ENNReal.ofReal_le_ofReal
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) h0))
  have hae : ∀ᵐ p ∂P.prod Q, Tendsto (fun n => F n p) atTop (𝓝 (L p.1)) := by
    refine (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hFmeas
      (hLmeas.comp measurable_fst))).2 ?_
    filter_upwards [ae_empirical_average_tendsto P ρ w hw hint] with ω hω
    filter_upwards [hω] with u hu
    exact ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hu)))
  have hdct := tendsto_lintegral_of_dominated_convergence (bound := fun _ : Ω × (ℕ → S) => (1 : ℝ≥0∞))
    hFmeas (fun n => ae_of_all _ (hbd n)) (by simp) hae
  have hprod_eq (n : ℕ) : (∫⁻ p, F n p ∂P.prod Q) = ∫⁻ u, ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      DOZZ.finiteChaosMass P (fun ω (i : Fin n) => Φ ω (u i.val))
        (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂P ∂Q := by
    rw [lintegral_prod _ (hFmeas n).aemeasurable,
      lintegral_lintegral_swap (hFmeas n).aemeasurable]
    refine lintegral_congr fun u => lintegral_congr fun ω => ?_
    simp only [F, DOZZ.finiteChaosMass, w, Finset.mul_sum]
    congr 2
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hlim_eq : (∫⁻ p, L p.1 ∂P.prod Q) = ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal)) ∂P := by
    rw [lintegral_prod (fun p : Ω × (ℕ → S) => L p.1) (hLmeas.comp measurable_fst).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    refine lintegral_congr_ae ?_
    filter_upwards [hint] with ω hω
    have hmass := fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hω
    have hnn : 0 ≤ lim ω := mul_nonneg (by positivity)
      (integral_nonneg fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _))
    rw [hmass]
    change L ω = ENNReal.ofReal (Real.exp (-s * (ENNReal.ofReal (lim ω)).toReal))
    rw [ENNReal.toReal_ofReal hnn]
  simpa only [hprod_eq, hlim_eq] using hdct

theorem centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral

    (ν : FiniteMeasure S) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hzero : ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) = 0) :
    ∀ ω, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω = 0 := by
  intro ω
  have hz : (fun x => (h x : ℝ) * Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Φ ω x))) =ᵐ[(ν.normalize : Measure S)] 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun x => NNReal.coe_nonneg (h x))
      (centeredGaussianField_bounded_weight_integrable ν h hh hhb)).mp hzero] with x hx
    simp [hx]
  rw [fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω
    ((integrable_congr hz).mpr (integrable_const 0)), integral_congr_ae hz]
  simp


end
section
variable [Nonempty S] (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ) (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) (hpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S))
include hΦ hν hh hhb γ hpos

theorem centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
 :
    ∀ᵐ ω ∂P, 0 < DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω := by
  have hsupp := (integral_pos_iff_support_of_nonneg (fun x => NNReal.coe_nonneg (h x))
    (centeredGaussianField_bounded_weight_integrable ν h hh hhb)).mp hpos
  filter_upwards [centeredGaussianField_ae_integrable_weighted_wick P Φ hΦ ν h hh hhb γ] with ω hω
  rw [fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hω]
  have hm : 0 < (ν.mass : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν)
  have hi : 0 < ∫ x, (h x : ℝ) * Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Φ ω x)) ∂(ν.normalize : Measure S) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun _ => mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)) hω,
      show (Function.support fun x => (h x : ℝ) * Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) = Function.support fun x => (h x : ℝ) by
        ext; simp [Real.exp_ne_zero]]
    exact hsupp
  positivity

theorem fieldChaosMass_eq_ofReal_modified_toReal_ae
 :
    let M := fun ω => DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω
    ∀ᵐ ω ∂P, M ω = ENNReal.ofReal ((fun ω => if (M ω).toReal = 0 then 1 else (M ω).toReal) ω) := by
  dsimp
  filter_upwards [centeredGaussianField_ae_integrable_weighted_wick P Φ hΦ ν h hh hhb γ,
    centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral P Φ hΦ ν hν h hh hhb γ hpos]
    with ω hω hposω
  have hf : DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ≠ ∞ := by
    rw [fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hω]; exact ENNReal.ofReal_ne_top
  simp [(ENNReal.toReal_pos hposω.ne' hf).ne', hf]


end
theorem kahane_field_laplace_of_nonzero_finite_measure_eq
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Nonempty S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ)
    (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c)
    (γ s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2))
    (hdiag : ∀ᵐ x ∂(ν : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX ≤
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY := by
  classical
  refine le_of_tendsto_of_tendsto
    (tendsto_lintegral_finiteChaosMass_laplace PX Φ hΦ ν h hh hhb γ s hs)
    (tendsto_lintegral_finiteChaosMass_laplace PY Ψ hΨ ν h hh hhb γ s hs)
    (Eventually.of_forall fun n => lintegral_mono_ae ?_)
  filter_upwards [centeredGaussianField_covariance_order_samples PX PY Φ Ψ hΦ hΨ ν hν hcov hdiag n]
    with u hu
  exact kahane_finite_laplace_lintegral_fintype PX PY _ _ (hΦ.2 n _) (hΨ.2 n _) _
    (fun _ => mul_nonneg (mul_nonneg (by positivity) (by positivity)) (NNReal.coe_nonneg _))
    γ s hs hu

private theorem fieldChaosMass_rpow_eq_mellin
 [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p < 0)
    (hpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S)) :
    ∫⁻ ω, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ^ p ∂P =
      ENNReal.ofReal (1 / Real.Gamma (-p)) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-p - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-t *
            (DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal)) ∂P) := by
  have := (hΦ.2 0 Fin.elim0).1
  let M : Ω → ℝ≥0∞ := DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ
  let m : Ω → ℝ := fun ω => if (M ω).toReal = 0 then 1 else (M ω).toReal
  have hMmeas := centeredGaussianField_fieldChaosMass_measurable P Φ hΦ (ν : Measure S) h hh γ
  have hmMeas : Measurable m := Measurable.ite
    (measurableSet_eq_fun hMmeas.ennreal_toReal measurable_const) measurable_const hMmeas.ennreal_toReal
  have hmPos (ω : Ω) : 0 < m ω := by dsimp [m]; split_ifs with hz <;> [norm_num; positivity]
  have hEq := fieldChaosMass_eq_ofReal_modified_toReal_ae P Φ hΦ ν hν h hh hhb γ hpos
  dsimp only at hEq
  have htoR : ∀ᵐ ω ∂P, (M ω).toReal = m ω := by
    filter_upwards [hEq] with ω hω
    dsimp only [M] at hω ⊢; rw [hω, ENNReal.toReal_ofReal (hmPos ω).le]
  have hMell := finite_rpow_neg_lintegral_eq_weighted_laplace P m hmPos hmMeas.aemeasurable (-p) (neg_pos.mpr hp)
  simp only [neg_neg] at hMell
  refine (lintegral_congr_ae ?_).trans (hMell.trans ?_)
  · filter_upwards [hEq] with ω hω; rw [hω]; rfl
  · congr 1
    refine lintegral_congr fun t => congrArg _ (lintegral_congr_ae ?_)
    filter_upwards [htoR] with ω hω
    rw [hω]; congr 2; ring

/-- Kahane's comparison for all nonpositive powers of continuum field chaos. -/
theorem kahane_field_power_nonpos
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : p ≤ 0)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ≤
      ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY := by
  have hPX := (hΦ.2 0 Fin.elim0).1
  have hPY := (hΨ.2 0 Fin.elim0).1
  by_cases hp0 : p = 0
  · simp [hp0, hPX.measure_univ, hPY.measure_univ]
  have hpneg := lt_of_le_of_ne hp hp0
  by_cases hν0 : ν = 0
  · have htop : ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY = ⊤ := by
      simp [DOZZ.fieldChaosMass, hν0, ENNReal.zero_rpow_of_neg hpneg, hPY.measure_univ]
    rw [htop]; exact le_top
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := fun hz => hν0 (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hz)
  obtain ⟨x₀, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_ne_zero.mpr hν0)
  have : Nonempty S := ⟨x₀⟩
  by_cases hα0 : ∫ x, (h x : ℝ) ∂(νf.normalize : Measure S) = 0
  · have hmY := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PY Ψ νf h hh hhb γ hα0
    have htop : ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY = ⊤ := by
      simp [show ν = (νf : Measure S) from rfl, hmY, ENNReal.zero_rpow_of_neg hpneg, hPY.measure_univ]
    rw [htop]; exact le_top
  have hαpos :=
    lt_of_le_of_ne (integral_nonneg fun _ => NNReal.coe_nonneg _) (Ne.symm hα0)
  change ∫⁻ ω, DOZZ.fieldChaosMass PX Φ (νf : Measure S) h γ ω ^ p ∂PX ≤
    ∫⁻ ω, DOZZ.fieldChaosMass PY Ψ (νf : Measure S) h γ ω ^ p ∂PY
  rw [fieldChaosMass_rpow_eq_mellin PX Φ hΦ νf hνf h hh hhb γ p hpneg hαpos,
    fieldChaosMass_rpow_eq_mellin PY Ψ hΨ νf hνf h hh hhb γ p hpneg hαpos]
  refine mul_le_mul_right ?_ _
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => mul_le_mul_right ?_ _
  exact kahane_field_laplace_of_nonzero_finite_measure_eq PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ t
    (Set.mem_Ioi.mp ht).le hcov
    (by filter_upwards [hdiag] with x hx; simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx)

end DOZZ.Proofs
