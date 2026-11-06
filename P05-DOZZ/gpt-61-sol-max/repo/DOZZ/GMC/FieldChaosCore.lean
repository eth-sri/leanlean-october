/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Probability.EmpiricalAverage

public import DOZZ.GMC.FiniteChaosNegativePower
public import DOZZ.GMC.FiniteChaosMean
public import DOZZ.GMC.Moments.ChaosLawFDD
public import DOZZ.Statements.GMC.FieldChaosMass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Batteries.Tactic.Alias

/-! Negative-power Kahane comparison for continuum Gaussian fields. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The covariance kernel of a jointly measurable centered Gaussian field is measurable. -/
theorem centeredGaussianField_covariance_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ) :
    Measurable (fun xy : S × S =>
      DOZZ.gaussianCovariance P (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2)) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have  := hzero.1
  let f : (S × S) × Ω → ℝ := fun q => Φ q.2 q.1.1 * Φ q.2 q.1.2
  have hf : Measurable f := by
    apply Measurable.mul
    · exact hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.1))
    · exact hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.2))
  have hint : Measurable (fun xy => ∫ ω, f (xy, ω) ∂P) := hf.stronglyMeasurable.integral_prod_right.measurable
  aesop

/-- The pointwise variance of a jointly measurable centered Gaussian field is measurable in its
spatial variable. -/
theorem centeredGaussianField_variance_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ) :
    Measurable (fun x => DOZZ.gaussianVariance P (fun ω => Φ ω x)) := (centeredGaussianField_covariance_measurable P Φ hΦ).comp
    (measurable_id.prodMk measurable_id)

/-- Every point evaluation of a centered Gaussian field has the centered Gaussian law whose
variance is its covariance-form diagonal. -/
theorem centeredGaussianField_pointwise_law
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ) (x : S) :
    HasLaw (fun ω => Φ ω x)
      (gaussianReal 0 (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal) P := by
  let Z : Ω → Fin 1 → ℝ := fun ω _ => Φ ω x
  have hZ  := hΦ.2 1 (fun _ => x)
  obtain ⟨v, hmap, _, hvar⟩ :=
    DOZZ.Proofs.coordinate_mean_variance P Z hZ (0 : Fin 1)
  have hv : (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal = v := by
    rw [hvar]
    simp
  refine ⟨hZ.2.1 0, ?_⟩
  simpa [Z, hv] using hmap

/-- A bounded nonnegative measurable weight is integrable under the normalized version of a
finite reference measure. -/
theorem centeredGaussianField_bounded_weight_integrable
    {S : Type*} [MeasurableSpace S] [Nonempty S] (ν : FiniteMeasure S)
    (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) :
    Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) := by
  obtain ⟨c, hc⟩ := hhb
  refine (integrable_const (c : ℝ)).mono'
    (measurable_coe_nnreal_real.comp hh).aestronglyMeasurable ?_
  simp_all

/-- Almost every field section has an integrable weighted Wick density under a probability
reference measure. -/
theorem centeredGaussianField_ae_integrable_weighted_wick
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have  := hzero.1
  have hv  :=
    measurable_real_toNNReal.comp (centeredGaussianField_variance_measurable P Φ hΦ)
  have hLaw  :=
    centeredGaussianField_pointwise_law P Φ hΦ
  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := integral_nonneg (fun ω => mul_self_nonneg (Φ ω x))
  have hsections := ae_integrable_weighted_wick_sections (ν.normalize : Measure S) Φ
    (fun x => (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal)
    (fun x => (h x : ℝ)) γ hΦ.1 hv (measurable_coe_nnreal_real.comp hh) hLaw
    (fun x => NNReal.coe_nonneg (h x))
    (centeredGaussianField_bounded_weight_integrable ν h hh hhb)
  simp_all

/-- The finite-cutoff field chaos mass is measurable. -/
theorem centeredGaussianField_fieldChaosMass_measurable
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) [SFinite ν] (h : S → ℝ≥0) (hh : Measurable h) (γ : ℝ) :
    Measurable (fun ω => DOZZ.fieldChaosMass P Φ ν h γ ω) := by
  have hv := centeredGaussianField_variance_measurable P Φ hΦ
  have hvInt : Measurable (fun x => ∫ ω, Φ ω x ^ 2 ∂P) := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hv
  have hfield  := hΦ.1
  have hvarInt : Measurable (fun q : Ω × S => ∫ ω, Φ ω q.2 ^ 2 ∂P) :=
    hvInt.comp measurable_snd
  have hlog : Measurable (fun q : Ω × S => γ * Φ q.1 q.2 - γ ^ 2 / 2 *
      (∫ ω, Φ ω q.2 ^ 2 ∂P)) := by fun_prop
  have hexp  := ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp hlog)
  have hf  :=
    (measurable_coe_nnreal_ennreal.comp (hh.comp measurable_snd)).mul hexp
  exact hf.lintegral_prod_right' (ν := ν)

theorem fieldChaosMass_eq_ofReal_normalized_integral
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω)
    (hint : Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S)) :
    DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω =
      ENNReal.ofReal ((ν.mass : ℝ) * ∫ x, (h x : ℝ) *
        Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Φ ω x)) ∂(ν.normalize : Measure S)) := by
  let f  := fun x => (h x : ℝ) *
    Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    bound
  have hintegrand (x : S) :
      (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P)) = ENNReal.ofReal (f x) := by
    have hv : DOZZ.gaussianVariance P (fun ω => Φ ω x) =
        ∫ ω', Φ ω' x ^ 2 ∂P := by
      noncomm_ring
    continuity
  unfold DOZZ.fieldChaosMass
  rw [show (fun x => (h x : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) =
      fun x => ENNReal.ofReal (f x) from funext hintegrand]
  rw [hνeq, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ hf_nonneg)]
  simp only [ENNReal.smul_def, smul_eq_mul]
  norm_num

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
  have hνeq  := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hρν : (ν.normalize : Measure S) ≪ (ν : Measure S) := by
    rw [hνeq]
    apply Measure.absolutelyContinuous_smul
    exact ENNReal.coe_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν)
  have hρprod  := hρν.prod hρν
  have hcvX := centeredGaussianField_covariance_measurable PX Φ hΦ
  have hcvY := centeredGaussianField_covariance_measurable PY Ψ hΨ
  have hvX := centeredGaussianField_variance_measurable PX Φ hΦ
  have hvY := centeredGaussianField_variance_measurable PY Ψ hΨ
  have hcovNorm : ∀ᵐ xy ∂(ν.normalize : Measure S).prod (ν.normalize : Measure S),
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) :=
    hρprod.ae_le hcov
  have hdiagNorm  := hρν.ae_le hdiag
  let Q  := Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S))

  have hpair (i j : ℕ) (hij : i ≠ j) :
      Q.map (fun u : ℕ → S => (u i, u j)) =
        (ν.normalize : Measure S).prod (ν.normalize : Measure S) := (Measure.infinitePi_map_eval_prod
      (P := fun _ : ℕ => (ν.normalize : Measure S)) hij)
  have heval (i : ℕ) : Q.map (fun u : ℕ → S => u i) =
      (ν.normalize : Measure S) := (Measure.infinitePi_map_eval (fun _ : ℕ => (ν.normalize : Measure S)) i)
  have hpairMeas (i j : ℕ) : Measurable (fun u : ℕ → S => (u i, u j)) := by
    fun_prop
  have hevalMeas (i : ℕ) : Measurable (fun u : ℕ → S => u i) := by
    fun_prop
  have hcovSample (i j : ℕ) (hij : i ≠ j) : ∀ᵐ u ∂Q,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i)) (fun ω => Φ ω (u j)) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i)) (fun ω => Ψ ω (u j)) := by
    have hset  :=
      measurableSet_le hcvX hcvY
    have hpull : ∀ᵐ u ∂Q.map (fun u : ℕ → S => (u i, u j)),
        DOZZ.gaussianCovariance PX (fun ω => Φ ω (u.1)) (fun ω => Φ ω (u.2)) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u.1)) (fun ω => Ψ ω (u.2)) := by
      rw [hpair i j hij]
      exact hcovNorm
    filter_upwards [(ae_map_iff (hpairMeas i j).aemeasurable hset).1 hpull] with u hu
    exact hu
  have hdiagSample (i : ℕ) : ∀ᵐ u ∂Q,
      DOZZ.gaussianVariance PX (fun ω => Φ ω (u i)) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i)) := by
    have hset  := measurableSet_le hvX hvY
    have hpull : ∀ᵐ x ∂Q.map (fun u : ℕ → S => u i),
        DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
          DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
      rw [heval i]
      exact hdiagNorm
    filter_upwards [(ae_map_iff (hevalMeas i).aemeasurable hset).1 hpull] with u hu
    exact hu
  intro n
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i.val = j.val
  · have hij'  := Fin.ext hij
    subst j
    exact hdiagSample i.val
  · exact hcovSample i.val j.val hij

private theorem lintegral_order_of_laplace_approximants
    {ΩX ΩY A : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace A]
    (PX : Measure ΩX) (PY : Measure ΩY) (Q : Measure A)
    [IsProbabilityMeasure PX] [IsProbabilityMeasure PY] [IsProbabilityMeasure Q]
    (FX : ℕ → ΩX × A → ℝ≥0∞) (FY : ℕ → ΩY × A → ℝ≥0∞)
    (LX : ΩX → ℝ≥0∞) (LY : ΩY → ℝ≥0∞)
    (hFX : ∀ n, Measurable (FX n)) (hFY : ∀ n, Measurable (FY n))
    (hLX : Measurable LX) (hLY : Measurable LY)
    (hboundX : ∀ n p, FX n p ≤ 1) (hboundY : ∀ n p, FY n p ≤ 1)
    (horder : ∀ n, ∫⁻ p, FX n p ∂PX.prod Q ≤ ∫⁻ p, FY n p ∂PY.prod Q)
    (hlimX : ∀ᵐ p ∂PX.prod Q, Tendsto (fun n => FX n p) atTop (𝓝 (LX p.1)))
    (hlimY : ∀ᵐ p ∂PY.prod Q, Tendsto (fun n => FY n p) atTop (𝓝 (LY p.1))) :
    ∫⁻ ω, LX ω ∂PX ≤ ∫⁻ ω, LY ω ∂PY := by
  have hfinX : ∫⁻ p, (1 : ℝ≥0∞) ∂PX.prod Q ≠ ∞ := by simp
  have hfinY : ∫⁻ p, (1 : ℝ≥0∞) ∂PY.prod Q ≠ ∞ := by simp
  have hDCTX := tendsto_lintegral_of_dominated_convergence
    (bound := fun _ : ΩX × A => (1 : ℝ≥0∞)) hFX
    (fun n => ae_of_all _ (hboundX n)) hfinX hlimX
  have hDCTY := tendsto_lintegral_of_dominated_convergence
    (bound := fun _ : ΩY × A => (1 : ℝ≥0∞)) hFY
    (fun n => ae_of_all _ (hboundY n)) hfinY hlimY
  have hprodX : ∫⁻ p, LX p.1 ∂PX.prod Q = ∫⁻ ω, LX ω ∂PX := by
    calc
      ∫⁻ p, LX p.1 ∂PX.prod Q = ∫⁻ ω, ∫⁻ a, LX ω ∂Q ∂PX :=
        lintegral_prod (fun p : ΩX × A => LX p.1)
          (hLX.comp measurable_fst).aemeasurable
      _ = ∫⁻ ω, LX ω ∂PX := by simp
  have hprodY : ∫⁻ p, LY p.1 ∂PY.prod Q = ∫⁻ ω, LY ω ∂PY := by
    calc
      ∫⁻ p, LY p.1 ∂PY.prod Q = ∫⁻ ω, ∫⁻ a, LY ω ∂Q ∂PY :=
        lintegral_prod (fun p : ΩY × A => LY p.1)
          (hLY.comp measurable_fst).aemeasurable
      _ = ∫⁻ ω, LY ω ∂PY := by simp
  rw [hprodX] at hDCTX
  rw [hprodY] at hDCTY
  exact le_of_tendsto_of_tendsto hDCTX hDCTY (Filter.Eventually.of_forall horder)

variable {ΩX ΩY S : Type*} [_inst1 : MeasurableSpace ΩX] [_inst2 : MeasurableSpace ΩY] [_inst3 : MeasurableSpace S] [_inst4 : Nonempty S] (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ) (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ) (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ s : ℝ) (hs : 0 ≤ s) (hcov : ∀ᵐ xy ∂(ν : Measure S).prod ν, DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤ DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2)) (hdiag : ∀ᵐ x ∂(ν : Measure S), DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤ DOZZ.gaussianVariance PY (fun ω => Ψ ω x))

include ΩX ΩY S _inst1 _inst2 _inst3 _inst4 PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ s hs hcov hdiag in
private theorem kahane_field_laplace_of_nonzero_finite_measure
     :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX ≤
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
      (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY := by
  classical
  have hPXzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have hPYzero := hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have  := hPXzero.1
  have  := hPYzero.1
  let ρ : Measure S := ν.normalize
  have hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have  := hρprob
  let Q  := Measure.infinitePi (fun _ : ℕ => ρ)
  have : IsProbabilityMeasure Q := by infer_instance
  let c  := (ν.mass : ℝ)
  let wx  := fun ω x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance PX (fun ω => Φ ω x))
  let wy  := fun ω x => (h x : ℝ) * Real.exp
    (γ * Ψ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance PY (fun ω => Ψ ω x))
  have hwickX : Measurable (fun p : ΩX × S => wx p.1 p.2) := by
    have hvar := centeredGaussianField_variance_measurable PX Φ hΦ
    have hvar' : Measurable (fun p : ΩX × S =>
        DOZZ.gaussianVariance PX (fun ω => Φ ω p.2)) := hvar.comp measurable_snd
    have hfield  := hΦ.1
    fun_prop
  have hwickY : Measurable (fun p : ΩY × S => wy p.1 p.2) := by
    have hvar := centeredGaussianField_variance_measurable PY Ψ hΨ
    have hvar' : Measurable (fun p : ΩY × S =>
        DOZZ.gaussianVariance PY (fun ω => Ψ ω p.2)) := hvar.comp measurable_snd
    have hfield  := hΨ.1
    fun_prop
  have hintX  := centeredGaussianField_ae_integrable_weighted_wick PX Φ hΦ ν h hh hhb γ
  have hintY  := centeredGaussianField_ae_integrable_weighted_wick PY Ψ hΨ ν h hh hhb γ
  have havgX := ae_empirical_average_tendsto PX ρ wx hwickX hintX
  have havgY := ae_empirical_average_tendsto PY ρ wy hwickY hintY
  have hρmeasX : Measurable (fun ω => ∫ x, wx ω x ∂ρ) :=
    hwickX.stronglyMeasurable.integral_prod_right'.measurable
  have hρmeasY : Measurable (fun ω => ∫ x, wy ω x ∂ρ) :=
    hwickY.stronglyMeasurable.integral_prod_right'.measurable
  let limitX  := fun ω => c * ∫ x, wx ω x ∂ρ
  let limitY  := fun ω => c * ∫ x, wy ω x ∂ρ
  let avgX : ℕ → ΩX × (ℕ → S) → ℝ := fun n p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, wx p.1 (p.2 i.val)
  let avgY : ℕ → ΩY × (ℕ → S) → ℝ := fun n p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, wy p.1 (p.2 i.val)
  let approxX  := fun n p => c * avgX n p
  let approxY  := fun n p => c * avgY n p
  let FX  := fun n p =>
    ENNReal.ofReal (Real.exp (-s * approxX n p))
  let FY  := fun n p =>
    ENNReal.ofReal (Real.exp (-s * approxY n p))


  have happroxXmeas (n : ℕ) : Measurable (fun p : ΩX × (ℕ → S) => approxX n p) := by
    fun_prop
  have happroxYmeas (n : ℕ) : Measurable (fun p : ΩY × (ℕ → S) => approxY n p) := by
    fun_prop
  have hFXmeas (n : ℕ) : Measurable (FX n) := by
    fun_prop
  have hFYmeas (n : ℕ) : Measurable (FY n) := by
    fun_prop
  have hformulaX (n : ℕ) (ω : ΩX) (u : ℕ → S) :
      DOZZ.finiteChaosMass PX (fun ω (i : Fin n) => Φ ω (u i.val))
        (fun (i : Fin n) => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω =
          approxX n (ω, u) := by
    simp only [DOZZ.finiteChaosMass]
    dsimp [approxX, avgX, wx]
    calc
      (∑ i : Fin n, (c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) *
          Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
            DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) =
          ∑ i : Fin n, (c * (n : ℝ)⁻¹) *
            ((h (u i.val) : ℝ) * Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) := by
                noncomm_ring
      _ = (c * (n : ℝ)⁻¹) * ∑ i : Fin n,
            ((h (u i.val) : ℝ) * Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) := by rw [Finset.mul_sum]
      _ = c * ((n : ℝ)⁻¹ * ∑ i : Fin n, wx ω (u i.val)) := by ring
  have hformulaY (n : ℕ) (ω : ΩY) (u : ℕ → S) :
      DOZZ.finiteChaosMass PY (fun ω (i : Fin n) => Ψ ω (u i.val))
        (fun (i : Fin n) => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω =
          approxY n (ω, u) := by
    simp only [DOZZ.finiteChaosMass]
    dsimp [approxY, avgY, wy]
    calc
      (∑ i : Fin n, (c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) *
          Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
            DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) =
          ∑ i : Fin n, (c * (n : ℝ)⁻¹) *
            ((h (u i.val) : ℝ) * Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) := by
                noncomm_ring
      _ = (c * (n : ℝ)⁻¹) * ∑ i : Fin n,
            ((h (u i.val) : ℝ) * Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) := by rw [Finset.mul_sum]
      _ = c * ((n : ℝ)⁻¹ * ∑ i : Fin n, wy ω (u i.val)) := by ring
  have hsample := centeredGaussianField_covariance_order_samples PX PY Φ Ψ hΦ hΨ
    ν hν hcov hdiag
  have hfiniteOrder (n : ℕ) : ∀ᵐ u ∂Q,
      (∫⁻ ω, FX n (ω, u) ∂PX) ≤ ∫⁻ ω, FY n (ω, u) ∂PY := by
    have hsampleN : ∀ᵐ u ∂Q,
        ∀ i j : Fin n,
          DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i.val)) (fun ω => Φ ω (u j.val)) ≤
            DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i.val)) (fun ω => Ψ ω (u j.val)) := hsample n
    filter_upwards [hsampleN] with u hu
    let Xn : ΩX → Fin n → ℝ := fun ω i => Φ ω (u i.val)
    let Yn : ΩY → Fin n → ℝ := fun ω i => Ψ ω (u i.val)
    have hXn  := hΦ.2 n (fun i => u i.val)
    have hYn  := hΨ.2 n (fun i => u i.val)
    have ha : ∀ i : Fin n, 0 ≤ c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ) := by
      intro i
      positivity
    have hfin := kahane_finite_laplace_lintegral_fintype PX PY Xn Yn hXn hYn
      (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) ha γ s hs
      (fun i j => hu i j)
    calc
      (∫⁻ ω, FX n (ω, u) ∂PX) =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
            DOZZ.finiteChaosMass PX Xn
              (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂PX := by
                apply lintegral_congr_ae
                exact ae_of_all _ fun ω => congrArg
                    (fun m : ℝ => ENNReal.ofReal (Real.exp (-s * m)))
                    (hformulaX n ω u).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
            DOZZ.finiteChaosMass PY Yn
              (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂PY := hfin
      _ = ∫⁻ ω, FY n (ω, u) ∂PY := by
            apply lintegral_congr_ae
            exact ae_of_all _ fun ω => congrArg
                (fun m : ℝ => ENNReal.ofReal (Real.exp (-s * m)))
                (hformulaY n ω u)
  have hproductOrder (n : ℕ) :
      ∫⁻ p, FX n p ∂PX.prod Q ≤ ∫⁻ p, FY n p ∂PY.prod Q := by
    have hswapX := lintegral_lintegral_swap (μ := PX) (ν := Q)
      (f := fun ω u => FX n (ω, u)) (hFXmeas n).aemeasurable
    have hswapY := lintegral_lintegral_swap (μ := PY) (ν := Q)
      (f := fun ω u => FY n (ω, u)) (hFYmeas n).aemeasurable
    calc
      _ = ∫⁻ u, ∫⁻ ω, FX n (ω, u) ∂PX ∂Q := by
        rw [lintegral_prod (FX n) (hFXmeas n).aemeasurable, hswapX]
      _ ≤ ∫⁻ u, ∫⁻ ω, FY n (ω, u) ∂PY ∂Q := lintegral_mono_ae (hfiniteOrder n)
      _ = ∫⁻ p, FY n p ∂PY.prod Q := by
        rw [lintegral_prod (FY n) (hFYmeas n).aemeasurable, hswapY]
  have hboundX (n : ℕ) (p : ΩX × (ℕ → S)) : FX n p ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, wx p.1 (p.2 i.val) := by
      positivity
    have havg : 0 ≤ avgX n p := by
      bound
    have happ : 0 ≤ approxX n p := by
      bound
    have hexp  :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) happ)
    simpa [FX] using ENNReal.ofReal_le_ofReal hexp
  have hboundY (n : ℕ) (p : ΩY × (ℕ → S)) : FY n p ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, wy p.1 (p.2 i.val) := by
      positivity
    have havg : 0 ≤ avgY n p := by
      bound
    have happ : 0 ≤ approxY n p := by
      bound
    have hexp  :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) happ)
    simpa [FY] using ENNReal.ofReal_le_ofReal hexp
  have hlimitXNested : ∀ᵐ ω ∂PX, ∀ᵐ u ∂Q,
      Tendsto (fun n => FX n (ω, u)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-s * limitX ω)))) := by
    have havgX' : ∀ᵐ ω ∂PX, ∀ᵐ u ∂Q,
        Tendsto (fun n => avgX n (ω, u)) atTop (𝓝 (∫ x, wx ω x ∂ρ)) := havgX
    filter_upwards [havgX'] with ω havg
    filter_upwards [havg] with u havg'
    have hmass : Tendsto (fun n => approxX n (ω, u)) atTop (𝓝 (limitX ω)) := tendsto_const_nhds.mul havg'
    have harg : Tendsto (fun n => -s * approxX n (ω, u)) atTop (𝓝 (-s * limitX ω)) :=
      tendsto_const_nhds.mul hmass
    have hexp := (Real.continuous_exp.tendsto (-s * limitX ω)).comp harg
    exact ENNReal.tendsto_ofReal hexp
  have hlimitYNested : ∀ᵐ ω ∂PY, ∀ᵐ u ∂Q,
      Tendsto (fun n => FY n (ω, u)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-s * limitY ω)))) := by
    have havgY' : ∀ᵐ ω ∂PY, ∀ᵐ u ∂Q,
        Tendsto (fun n => avgY n (ω, u)) atTop (𝓝 (∫ x, wy ω x ∂ρ)) := havgY
    filter_upwards [havgY'] with ω havg
    filter_upwards [havg] with u havg'
    have hmass : Tendsto (fun n => approxY n (ω, u)) atTop (𝓝 (limitY ω)) := tendsto_const_nhds.mul havg'
    have harg : Tendsto (fun n => -s * approxY n (ω, u)) atTop (𝓝 (-s * limitY ω)) :=
      tendsto_const_nhds.mul hmass
    have hexp := (Real.continuous_exp.tendsto (-s * limitY ω)).comp harg
    exact ENNReal.tendsto_ofReal hexp
  have hlimitMeasX : Measurable (fun p : ΩX × (ℕ → S) =>
      ENNReal.ofReal (Real.exp (-s * limitX p.1))) := by
    fun_prop
  have hlimitMeasY : Measurable (fun p : ΩY × (ℕ → S) =>
      ENNReal.ofReal (Real.exp (-s * limitY p.1))) := by
    fun_prop
  have hseqMeasX  := hFXmeas
  have hseqMeasY  := hFYmeas
  have hsetX  := measurableSet_tendsto_fun (l := atTop) hseqMeasX hlimitMeasX
  have hsetY  := measurableSet_tendsto_fun (l := atTop) hseqMeasY hlimitMeasY
  have hlimitX  :=
    Measure.ae_prod_iff_ae_ae hsetX |>.2 hlimitXNested
  have hlimitY  :=
    Measure.ae_prod_iff_ae_ae hsetY |>.2 hlimitYNested
  have hlimitOrder := lintegral_order_of_laplace_approximants PX PY Q FX FY
    (fun ω => ENNReal.ofReal (Real.exp (-s * limitX ω)))
    (fun ω => ENNReal.ofReal (Real.exp (-s * limitY ω)))
    hFXmeas hFYmeas
    (ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hρmeasX))))
    (ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_const.mul hρmeasY))))
    hboundX hboundY hproductOrder hlimitX hlimitY
  have htargetX :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
        (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal)) ∂PX =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitX ω)) ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hintX] with ω hInt
    have hfieldMass := fieldChaosMass_eq_ofReal_normalized_integral PX Φ ν h γ ω
      (hInt)
    have hlimNonneg : 0 ≤ limitX ω := by
      positivity
    have htoReal : (DOZZ.fieldChaosMass PX Φ (ν : Measure S) h γ ω).toReal = limitX ω := by
      rw [hfieldMass]
      exact ENNReal.toReal_ofReal hlimNonneg
    rw [htoReal]
  have htargetY :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
        (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal)) ∂PY =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitY ω)) ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hintY] with ω hInt
    have hfieldMass := fieldChaosMass_eq_ofReal_normalized_integral PY Ψ ν h γ ω
      (hInt)
    have hlimNonneg : 0 ≤ limitY ω := by
      positivity
    have htoReal : (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal = limitY ω := by
      rw [hfieldMass]
      exact ENNReal.toReal_ofReal hlimNonneg
    rw [htoReal]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitX ω)) ∂PX := htargetX
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-s * limitY ω)) ∂PY := hlimitOrder
    _ = _ := htargetY.symm

theorem centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hzero : ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) = 0) :
    ∀ ω, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω = 0 := by
  have hbaseInt  :=
    centeredGaussianField_bounded_weight_integrable ν h hh hhb
  have hbaseZero  :=
    (integral_eq_zero_iff_of_nonneg (fun x => NNReal.coe_nonneg (h x)) hbaseInt).mp hzero
  intro ω
  let f  := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hzeroF : f =ᵐ[(ν.normalize : Measure S)] 0 := by
    filter_upwards [hbaseZero] with x hx
    simp [f, hx]
  have hIntF  :=
    (integrable_congr hzeroF).mpr (integrable_const (0 : ℝ))
  have hmass := fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hIntF
  rw [hmass]
  have hfint : ∫ x, f x ∂(ν.normalize : Measure S) = 0 := by
    rw [integral_congr_ae hzeroF]
    simp
  rw [hfint]
  simp

theorem centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S)) :
    ∀ᵐ ω ∂P, 0 < DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω := by
  have hbaseInt  :=
    centeredGaussianField_bounded_weight_integrable ν h hh hhb
  have hbaseSupport  :=
    (integral_pos_iff_support_of_nonneg
      (f := fun x => (h x : ℝ)) (μ := (ν.normalize : Measure S))
      (fun x => NNReal.coe_nonneg (h x)) hbaseInt).mp hpos
  have hPzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)

  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    obtain ⟨v, _, _, hvar⟩ :=
      DOZZ.Proofs.coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x)
        (hΦ.2 1 (fun _ => x)) (0 : Fin 1)
    rw [hvar]
    positivity
  have hint := centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ
  filter_upwards [hint] with ω hω
  let f  := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hf_nonneg (x : S) : 0 ≤ f x :=
    mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
  have hfsupport : Function.support f = Function.support fun x => (h x : ℝ) := by
    continuity
  have hfpos : 0 < ∫ x, f x ∂(ν.normalize : Measure S) := by
    rw [integral_pos_iff_support_of_nonneg hf_nonneg hω, hfsupport]
    exact hbaseSupport
  have hrepresentation := fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω (hω)
  have hmasspos : 0 < (ν.mass : ℝ) := by
    have hmassne  := ν.mass_nonzero_iff.mpr hν
    positivity
  rw [hrepresentation]
  positivity

/-- A field-chaos mass is finite almost surely under a bounded spatial weight. -/
theorem centeredGaussianField_fieldChaosMass_ne_top_ae
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ≠ ∞ := by
  filter_upwards [centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ] with ω hω
  rw [fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω hω]
  exact ENNReal.ofReal_ne_top

include ΩX ΩY S _inst1 _inst2 _inst3 _inst4 PX PY Φ Ψ hΦ hΨ ν hν h hh hhb γ s hs hcov hdiag in
alias kahane_field_laplace_of_nonzero_finite_measure_eq := DOZZ.Proofs.kahane_field_laplace_of_nonzero_finite_measure


end DOZZ.Proofs
