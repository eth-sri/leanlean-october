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

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ)
  (hΦ : DOZZ.IsCenteredGaussianField P Φ)
include Ω S hΦ

/-- The pointwise variance of a jointly measurable centered Gaussian field is measurable in its
spatial variable. -/
theorem centeredGaussianField_variance_measurable :
    Measurable (fun x => DOZZ.gaussianVariance P (fun ω => Φ ω x)) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have hPprob  := hzero.1
  let f : S × Ω → ℝ := fun q => Φ q.2 q.1
  have hf := hΦ.1.comp (by fun_prop : Measurable fun q : S × Ω => (q.2, q.1))
  have hf2  := hf.mul hf
  have hint : Measurable (fun x => ∫ ω, f (x, ω) * f (x, ω) ∂P) := hf2.stronglyMeasurable.integral_prod_right.measurable
  assumption

/-- The covariance kernel of a jointly measurable centered Gaussian field is measurable. -/
theorem centeredGaussianField_covariance_measurable :
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
  assumption

/-- Every point evaluation of a centered Gaussian field has the centered Gaussian law whose
variance is its covariance-form diagonal. -/
theorem centeredGaussianField_pointwise_law (x : S) :
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
    (measurable_coe_nnreal_real.comp hh).aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg (h x))]
  exact_mod_cast hc x

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Almost every field section has an integrable weighted Wick density under a probability
reference measure. -/
theorem centeredGaussianField_ae_integrable_weighted_wick [Nonempty S]
    (P : Measure Ω) (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : FiniteMeasure S) (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun x => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Φ ω x))) (ν.normalize : Measure S) := by
  have hzero := hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have  := hzero.1
  have hv := measurable_real_toNNReal.comp (centeredGaussianField_variance_measurable P Φ hΦ)
  have hLaw := centeredGaussianField_pointwise_law P Φ hΦ
  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    obtain ⟨v, _, _, hvar⟩ :=
      DOZZ.Proofs.coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x)
        (hΦ.2 1 (fun _ => x)) (0 : Fin 1)
    rw [hvar]
    positivity
  have hsections := ae_integrable_weighted_wick_sections (ν.normalize : Measure S) Φ
    (fun x => (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal)
    (fun x => (h x : ℝ)) γ hΦ.1 hv (measurable_coe_nnreal_real.comp hh) hLaw
    (fun x => NNReal.coe_nonneg (h x))
    (centeredGaussianField_bounded_weight_integrable ν h hh hhb)
  filter_upwards [hsections] with ω hω
  exact hω.congr (ae_of_all _ fun x => congrFun (by
    funext x
    exact congrArg (fun t : ℝ => (h x : ℝ) *
      Real.exp (γ * Φ ω x - γ ^ 2 / 2 * t))
      (Real.coe_toNNReal _ (hvar_nonneg x))) x)

/-- The finite-cutoff field chaos mass is measurable. -/
theorem centeredGaussianField_fieldChaosMass_measurable
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
  have hexp := ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp hlog)
  have hf := (measurable_coe_nnreal_ennreal.comp (hh.comp measurable_snd)).mul hexp
  unfold DOZZ.fieldChaosMass
  exact hf.lintegral_prod_right' (ν := ν)

theorem fieldChaosMass_eq_ofReal_normalized_integral [Nonempty S]
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
    Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
  have hintegrand (x : S) :
      (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P)) = ENNReal.ofReal (f x) := by
    have hv : DOZZ.gaussianVariance P (fun ω => Φ ω x) =
        ∫ ω', Φ ω' x ^ 2 ∂P := by
      simp [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two]
    rw [← hv]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg (h x))]
  unfold DOZZ.fieldChaosMass
  rw [show (fun x => (h x : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P))) =
      fun x => ENNReal.ofReal (f x) from funext hintegrand]
  rw [hνeq, lintegral_smul_measure]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ hf_nonneg)]
  simp only [ENNReal.smul_def, smul_eq_mul]
  simp

end

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
  have hνeq := congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hρν : (ν.normalize : Measure S) ≪ (ν : Measure S) := by
    rw [hνeq]
    apply Measure.absolutelyContinuous_smul
    exact ENNReal.coe_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν)
  have hρprod := hρν.prod hρν
  have hcvX := centeredGaussianField_covariance_measurable PX Φ hΦ
  have hcvY := centeredGaussianField_covariance_measurable PY Ψ hΨ
  have hvX := centeredGaussianField_variance_measurable PX Φ hΦ
  have hvY := centeredGaussianField_variance_measurable PY Ψ hΨ
  have hcovNorm := hρprod.ae_le hcov
  have hdiagNorm := hρν.ae_le hdiag
  let Q  := Measure.infinitePi (fun _ : ℕ => (ν.normalize : Measure S))
  have hpair (i j : ℕ) (hij : i ≠ j) :
      Q.map (fun u : ℕ → S => (u i, u j)) =
        (ν.normalize : Measure S).prod (ν.normalize : Measure S) := by
    simpa [Q] using (Measure.infinitePi_map_eval_prod
      (P := fun _ : ℕ => (ν.normalize : Measure S)) hij)
  have heval (i : ℕ) : Q.map (fun u : ℕ → S => u i) =
      (ν.normalize : Measure S) := by
    simpa [Q] using
      (Measure.infinitePi_map_eval (fun _ : ℕ => (ν.normalize : Measure S)) i)
  have hpairMeas (i j : ℕ) : Measurable (fun u : ℕ → S => (u i, u j)) := by
    fun_prop
  have hevalMeas (i : ℕ) : Measurable (fun u : ℕ → S => u i) := by
    fun_prop
  have hcovSample (i j : ℕ) (hij : i ≠ j) : ∀ᵐ u ∂Q,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i)) (fun ω => Φ ω (u j)) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i)) (fun ω => Ψ ω (u j)) := by
    have hset := measurableSet_le hcvX hcvY
    have hpull : ∀ᵐ u ∂Q.map (fun u : ℕ → S => (u i, u j)),
        DOZZ.gaussianCovariance PX (fun ω => Φ ω (u.1)) (fun ω => Φ ω (u.2)) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u.1)) (fun ω => Ψ ω (u.2)) := by
      rwa [hpair i j hij]
    filter_upwards [(ae_map_iff (hpairMeas i j).aemeasurable hset).1 hpull] with u hu
    exact hu
  have hdiagSample (i : ℕ) : ∀ᵐ u ∂Q,
      DOZZ.gaussianVariance PX (fun ω => Φ ω (u i)) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i)) := by
    have hset := measurableSet_le hvX hvY
    have hpull : ∀ᵐ x ∂Q.map (fun u : ℕ → S => u i),
        DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
          DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
      rwa [heval i]
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
  · apply hcovSample <;> assumption

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S] (P : Measure Ω)
  (Φ : Ω → S → ℝ)
include Ω

theorem centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
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
  have hint := centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ
  filter_upwards [hint] with ω hω
  let f  := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hf_nonneg (x : S) : 0 ≤ f x :=
    mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
  have hfsupport : Function.support f = Function.support fun x => (h x : ℝ) := by
    ext x
    simp [f, Function.mem_support, Real.exp_ne_zero]
  have hfpos : 0 < ∫ x, f x ∂(ν.normalize : Measure S) := by
    rwa [integral_pos_iff_support_of_nonneg hf_nonneg hω, hfsupport]
  have hrepresentation := fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω (by simpa [f] using hω)
  have hmasspos : 0 < (ν.mass : ℝ) := by
    have hmassne  := ν.mass_nonzero_iff.mpr hν
    exact_mod_cast (pos_iff_ne_zero.mpr hmassne : 0 < ν.mass)
  rw [hrepresentation]
  exact ENNReal.ofReal_pos.mpr (mul_pos hmasspos hfpos)

end

end DOZZ.Proofs
