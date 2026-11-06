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
section
variable (hΦ : DOZZ.IsCenteredGaussianField P Φ)
include hΦ

/-- The pointwise variance of a jointly measurable centered Gaussian field is measurable in its
spatial variable. -/
theorem centeredGaussianField_variance_measurable
    :
    Measurable (fun x => DOZZ.gaussianVariance P (fun ω => Φ ω x)) := by
  have hPprob := (hΦ.2 0 Fin.elim0).1
  let f : S × Ω → ℝ := fun q => Φ q.2 q.1
  have hf : Measurable f := by
    exact hΦ.1.comp (by fun_prop : Measurable fun q : S × Ω => (q.2, q.1))
  exact (hf.mul hf).stronglyMeasurable.integral_prod_right.measurable

/-- The covariance kernel of a jointly measurable centered Gaussian field is measurable. -/
theorem centeredGaussianField_covariance_measurable
    :
    Measurable (fun xy : S × S =>
      DOZZ.gaussianCovariance P (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2)) := by
  have : IsProbabilityMeasure P := (hΦ.2 0 Fin.elim0).1
  let f : (S × S) × Ω → ℝ := fun q => Φ q.2 q.1.1 * Φ q.2 q.1.2
  have hf : Measurable f := by
    apply Measurable.mul
    · exact hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.1))
    · exact hΦ.1.comp (by fun_prop : Measurable fun q : (S × S) × Ω => (q.2, q.1.2))
  exact hf.stronglyMeasurable.integral_prod_right.measurable

/-- Every point evaluation of a centered Gaussian field has the centered Gaussian law whose
variance is its covariance-form diagonal. -/
theorem centeredGaussianField_pointwise_law
    (x : S) :
    HasLaw (fun ω => Φ ω x)
      (gaussianReal 0 (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal) P := by
  let Z : Ω → Fin 1 → ℝ := fun ω _ => Φ ω x
  have hZ := hΦ.2 1 (fun _ => x)
  obtain ⟨v, hmap, _, hvar⟩ :=
    DOZZ.Proofs.coordinate_mean_variance P Z hZ 0
  have hv : (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal = v := by
    aesop
  refine ⟨hZ.2.1 0, ?_⟩
  aesop

end

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
  simp_all
section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

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
  have : IsProbabilityMeasure P := (hΦ.2 0 Fin.elim0).1
  have hv :=
    measurable_real_toNNReal.comp (centeredGaussianField_variance_measurable P Φ hΦ)
  have hLaw :=
    centeredGaussianField_pointwise_law P Φ hΦ
  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    obtain ⟨v, _, _, hvar⟩ :=
      DOZZ.Proofs.coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x)
        (hΦ.2 1 (fun _ => x)) 0
    simp_all
  have hsections := ae_integrable_weighted_wick_sections ν.normalize Φ
    (fun x => (DOZZ.gaussianVariance P (fun ω => Φ ω x)).toNNReal)
    (fun x => (h x)) γ hΦ.1 hv (measurable_coe_nnreal_real.comp hh) hLaw
    (fun x => NNReal.coe_nonneg (h x))
    (centeredGaussianField_bounded_weight_integrable ν h hh hhb)
  simp_all
section
variable (P : Measure Ω)

/-- The finite-cutoff field chaos mass is measurable. -/
theorem centeredGaussianField_fieldChaosMass_measurable
    (Φ : Ω → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField P Φ)
    (ν : Measure S) [SFinite ν] (h : S → ℝ≥0) (hh : Measurable h) (γ : ℝ) :
    Measurable (fun ω => DOZZ.fieldChaosMass P Φ ν h γ ω) := by
  have hvInt : Measurable (fun x => ∫ ω, Φ ω x ^ 2 ∂P) := by
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using (centeredGaussianField_variance_measurable P Φ hΦ)
  have hfield : Measurable (fun q : Ω × S => Φ q.1 q.2) := hΦ.1
  have hvarInt : Measurable (fun q : Ω × S => ∫ ω, Φ ω q.2 ^ 2 ∂P) :=
    hvInt.comp measurable_snd
  have hlog : Measurable (fun q : Ω × S => γ * Φ q.1 q.2 - γ ^ 2 / 2 *
      (∫ ω, Φ ω q.2 ^ 2 ∂P)) := by fun_prop
  have hexp : Measurable (fun q : Ω × S => ENNReal.ofReal
      (Real.exp (γ * Φ q.1 q.2 - γ ^ 2 / 2 *
        (∫ ω, Φ ω q.2 ^ 2 ∂P)))) := by fun_prop
  have hf :=
    (measurable_coe_nnreal_ennreal.comp (hh.comp measurable_snd)).mul hexp
  unfold DOZZ.fieldChaosMass
  fun_prop

theorem ae_empirical_average_tendsto
    (ν : Measure S) [IsProbabilityMeasure ν]
    (f : Ω → S → ℝ)
    (hjoint : Measurable (fun p : Ω × S => f p.1 p.2))
    (hint : ∀ᵐ ω ∂P, Integrable (f ω) ν) :
    ∀ᵐ ω ∂P, ∀ᵐ q ∂Measure.infinitePi (fun _ : ℕ => ν),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ => ν)
  have hQ : IsProbabilityMeasure Q := by infer_instance
  have hEvalIdent (i : ℕ) : IdentDistrib (fun q => q i) id Q ν := by
    refine ⟨(measurable_pi_apply i).aemeasurable, aemeasurable_id, ?_⟩
    simpa [Q] using (Measure.infinitePi_map_eval (fun _ => ν) i)
  have hCoordIdent (i : ℕ) :
      IdentDistrib (fun q => q i) (fun q => q 0) Q Q :=
    (hEvalIdent i).trans (hEvalIdent 0).symm
  have hindepCoord : iIndepFun (fun i (q : ℕ → S) => q i) Q := by
    simpa [Q] using
      (iIndepFun_infinitePi (X := fun _ : ℕ => id)
        (by fun_prop))
  have hInner (ω : Ω) (hω : Integrable (f ω) ν) :
      ∀ᵐ q ∂Q,
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
          atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    have hfmeas :=
      hjoint.comp (by fun_prop : Measurable fun x => (ω, x))
    have hindep' : Pairwise (fun i j =>
        (fun q => f ω (q i)) ⟂ᵢ[Q] (fun q => f ω (q j))) := by
      intro i j hij
      exact (hindepCoord.comp (fun _ => f ω) (fun _ => hfmeas)).indepFun hij
    have hident : ∀ i, IdentDistrib (fun q => f ω (q i))
        (fun q => f ω (q 0)) Q Q := by
      intro i
      exact (hCoordIdent i).comp hfmeas
    have hsampleIdent :=
      (hEvalIdent 0).comp hfmeas
    have hsampleInt :=
      hsampleIdent.integrable_iff.mpr hω
    have hmean : (∫ q, f ω (q 0) ∂Q) = ∫ x, f ω x ∂ν :=
      hsampleIdent.integral_eq
    have hlln := ProbabilityTheory.strong_law_ae
      (fun i (q : ℕ → S) => f ω (q i)) hsampleInt hindep' hident
    filter_upwards [hlln] with q hq
    simpa only [smul_eq_mul, ← Fin.sum_univ_eq_sum_range, hmean] using hq
  have hIter : ∀ᵐ ω ∂P, ∀ᵐ q ∂Q,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, f ω (q i.val))
        atTop (𝓝 (∫ x, f ω x ∂ν)) := by
    filter_upwards [hint] with ω hω
    exact hInner ω hω
  exact hIter

end

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
    Real.exp (γ * Φ ω x - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := by
    exact congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    bound
  have hintegrand (x : S) :
      (h x : ℝ≥0∞) * ENNReal.ofReal (Real.exp
        (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P)) = ENNReal.ofReal (f x) := by
    have hv : DOZZ.gaussianVariance P (fun ω => Φ ω x) =
        ∫ ω', Φ ω' x ^ 2 ∂P := by
      simp [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two]
    aesop
  unfold DOZZ.fieldChaosMass
  rw [show (fun x => (h x : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp _)) =
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
  have hνeq : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) := by
    exact congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hρν : (ν.normalize : Measure S) ≪ (ν : Measure S) := by
    rw [hνeq]
    apply Measure.absolutelyContinuous_smul
    exact ENNReal.coe_ne_zero.mpr (ν.mass_nonzero_iff.mpr hν)
  have hρprod : (ν.normalize : Measure S).prod (ν.normalize : Measure S) ≪
      (ν : Measure S).prod ν := hρν.prod hρν
  have hvX := centeredGaussianField_variance_measurable PX Φ hΦ
  have hvY := centeredGaussianField_variance_measurable PY Ψ hΨ
  have hcovNorm : ∀ᵐ xy ∂(ν.normalize : Measure S).prod (ν.normalize : Measure S),
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) :=
    hρprod.ae_le hcov
  have hdiagNorm : ∀ᵐ x ∂(ν.normalize : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := hρν.ae_le hdiag
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ => (ν.normalize : Measure S))
  have hQ : IsProbabilityMeasure Q := by infer_instance
  have hpair (i j : ℕ) (hij : i ≠ j) :
      Q.map (fun u => (u i, u j)) =
        (ν.normalize : Measure S).prod (ν.normalize : Measure S) := by
    simpa [Q] using (Measure.infinitePi_map_eval_prod
      hij)
  have heval (i : ℕ) : Q.map (fun u => u i) =
      (ν.normalize : Measure S) := by
    simpa [Q] using
      (Measure.infinitePi_map_eval (fun _ => (ν.normalize : Measure S)) i)
  have hpairMeas (i j : ℕ) : Measurable (fun u : ℕ → S => (u i, u j)) := by
    fun_prop
  have hevalMeas (i : ℕ) : Measurable (fun u : ℕ → S => u i) := by
    fun_prop
  have hcovSample (i j : ℕ) (hij : i ≠ j) : ∀ᵐ u ∂Q,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω (u i)) (fun ω => Φ ω (u j)) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i)) (fun ω => Ψ ω (u j)) := by
    have hset : MeasurableSet {xy : S × S |
        DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2)} :=
      measurableSet_le (centeredGaussianField_covariance_measurable PX Φ hΦ) (centeredGaussianField_covariance_measurable PY Ψ hΨ)
    have hpull : ∀ᵐ u ∂Q.map (fun u => (u i, u j)),
        DOZZ.gaussianCovariance PX (fun ω => Φ ω (u.1)) (fun ω => Φ ω (u.2)) ≤
          DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u.1)) (fun ω => Ψ ω (u.2)) := by
      rw [hpair i j hij]
      exact hcovNorm
    filter_upwards [(ae_map_iff (hpairMeas i j).aemeasurable hset).1 hpull] with u hu
    exact hu
  have hdiagSample (i : ℕ) : ∀ᵐ u ∂Q,
      DOZZ.gaussianVariance PX (fun ω => Φ ω (u i)) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i)) := by
    have hset : MeasurableSet {x : S |
        DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
          DOZZ.gaussianVariance PY (fun ω => Ψ ω x)} := measurableSet_le hvX hvY
    have hpull : ∀ᵐ x ∂Q.map (fun u => u i),
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
  · have hij' : i = j := Fin.ext hij
    bound
  · tauto

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
  have hfinX : ∫⁻ p, 1 ∂PX.prod Q ≠ ∞ := by simp
  have hfinY : ∫⁻ p, 1 ∂PY.prod Q ≠ ∞ := by simp
  have hDCTX := tendsto_lintegral_of_dominated_convergence
    (bound := fun _ : ΩX × A => 1) hFX
    (fun n => ae_of_all _ (hboundX n)) hfinX hlimX
  have hDCTY := tendsto_lintegral_of_dominated_convergence
    (bound := fun _ : ΩY × A => 1) hFY
    (fun n => ae_of_all _ (hboundY n)) hfinY hlimY
  have hprodX : ∫⁻ p, LX p.1 ∂PX.prod Q = ∫⁻ ω, LX ω ∂PX := by
    calc
      ∫⁻ p, LX p.1 ∂PX.prod Q = ∫⁻ ω, ∫⁻ a, LX ω ∂Q ∂PX :=
        lintegral_prod (fun p => LX p.1)
          (hLX.comp measurable_fst).aemeasurable
      _ = ∫⁻ ω, LX ω ∂PX := by simp
  have hprodY : ∫⁻ p, LY p.1 ∂PY.prod Q = ∫⁻ ω, LY ω ∂PY := by
    calc
      ∫⁻ p, LY p.1 ∂PY.prod Q = ∫⁻ ω, ∫⁻ a, LY ω ∂Q ∂PY :=
        lintegral_prod (fun p => LY p.1)
          (hLY.comp measurable_fst).aemeasurable
      _ = ∫⁻ ω, LY ω ∂PY := by simp
  rw [hprodX] at hDCTX
  rw [hprodY] at hDCTY
  exact le_of_tendsto_of_tendsto hDCTX hDCTY (Filter.Eventually.of_forall horder)

theorem kahane_field_laplace_of_nonzero_finite_measure
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
  have : IsProbabilityMeasure PX := (hΦ.2 0 Fin.elim0).1
  have : IsProbabilityMeasure PY := (hΨ.2 0 Fin.elim0).1
  let ρ : Measure S := ν.normalize
  have hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have : IsProbabilityMeasure ρ := hρprob
  let Q : Measure (ℕ → S) := Measure.infinitePi (fun _ => ρ)
  have : IsProbabilityMeasure Q := by infer_instance
  let c := (ν.mass : ℝ)
  let wx : ΩX → S → ℝ := fun ω x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance PX (fun ω => Φ ω x))
  let wy : ΩY → S → ℝ := fun ω x => (h x : ℝ) * Real.exp
    (γ * Ψ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance PY (fun ω => Ψ ω x))
  have hwickX : Measurable (fun p : ΩX × S => wx p.1 p.2) := by
    have hvar := centeredGaussianField_variance_measurable PX Φ hΦ
    have hvar' : Measurable (fun p : ΩX × S =>
        DOZZ.gaussianVariance PX (fun ω => Φ ω p.2)) := hvar.comp measurable_snd
    have hfield : Measurable (fun p : ΩX × S => Φ p.1 p.2) := hΦ.1
    have hweight : Measurable (fun p : ΩX × S => (h p.2 : ℝ)) :=
      by fun_prop
    have hlog : Measurable (fun p : ΩX × S => γ * Φ p.1 p.2 - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PX (fun ω => Φ ω p.2)) :=
      by fun_prop
    exact hweight.mul (Real.measurable_exp.comp hlog)
  have hwickY : Measurable (fun p : ΩY × S => wy p.1 p.2) := by
    have hvar := centeredGaussianField_variance_measurable PY Ψ hΨ
    have hvar' : Measurable (fun p : ΩY × S =>
        DOZZ.gaussianVariance PY (fun ω => Ψ ω p.2)) := hvar.comp measurable_snd
    have hfield : Measurable (fun p : ΩY × S => Ψ p.1 p.2) := hΨ.1
    have hweight : Measurable (fun p : ΩY × S => (h p.2 : ℝ)) :=
      by fun_prop
    have hlog : Measurable (fun p : ΩY × S => γ * Ψ p.1 p.2 - γ ^ 2 / 2 *
        DOZZ.gaussianVariance PY (fun ω => Ψ ω p.2)) :=
      by fun_prop
    exact hweight.mul (Real.measurable_exp.comp hlog)
  have hintX : ∀ᵐ ω ∂PX, Integrable (wx ω) ρ := by
    simpa [wx, ρ] using centeredGaussianField_ae_integrable_weighted_wick
      PX Φ hΦ ν h hh hhb γ
  have hintY : ∀ᵐ ω ∂PY, Integrable (wy ω) ρ := by
    simpa [wy, ρ] using centeredGaussianField_ae_integrable_weighted_wick
      PY Ψ hΨ ν h hh hhb γ
  have hρmeasX : Measurable (fun ω => ∫ x, wx ω x ∂ρ) :=
    hwickX.stronglyMeasurable.integral_prod_right'.measurable
  have hρmeasY : Measurable (fun ω => ∫ x, wy ω x ∂ρ) :=
    hwickY.stronglyMeasurable.integral_prod_right'.measurable
  let limitX : ΩX → ℝ := fun ω => c * ∫ x, wx ω x ∂ρ
  let limitY : ΩY → ℝ := fun ω => c * ∫ x, wy ω x ∂ρ
  let avgX : ℕ → ΩX × (ℕ → S) → ℝ := fun n p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, wx p.1 (p.2 i.val)
  let avgY : ℕ → ΩY × (ℕ → S) → ℝ := fun n p =>
    (n : ℝ)⁻¹ * ∑ i : Fin n, wy p.1 (p.2 i.val)
  let approxX : ℕ → ΩX × (ℕ → S) → ℝ := fun n p => c * avgX n p
  let approxY : ℕ → ΩY × (ℕ → S) → ℝ := fun n p => c * avgY n p
  let FX : ℕ → ΩX × (ℕ → S) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-s * approxX n p))
  let FY : ℕ → ΩY × (ℕ → S) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (-s * approxY n p))
  have htermX (n : ℕ) (i : Fin n) :
      Measurable (fun p : ΩX × (ℕ → S) => wx p.1 (p.2 i.val)) := by
    have harg : Measurable (fun p : ΩX × (ℕ → S) => (p.1, p.2 i.val)) :=
      by fun_prop
    exact hwickX.comp harg
  have htermY (n : ℕ) (i : Fin n) :
      Measurable (fun p : ΩY × (ℕ → S) => wy p.1 (p.2 i.val)) := by
    have harg : Measurable (fun p : ΩY × (ℕ → S) => (p.1, p.2 i.val)) :=
      by fun_prop
    exact hwickY.comp harg
  have happroxXmeas (n : ℕ) : Measurable (approxX n) := by
    apply measurable_const.mul
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact htermX n i
  have happroxYmeas (n : ℕ) : Measurable (approxY n) := by
    apply measurable_const.mul
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i hi
    exact htermY n i
  have hFXmeas (n : ℕ) : Measurable (FX n) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (happroxXmeas n)))
  have hFYmeas (n : ℕ) : Measurable (FY n) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul (happroxYmeas n)))
  have hformulaX (n : ℕ) (ω : ΩX) (u : ℕ → S) :
      DOZZ.finiteChaosMass PX (fun ω (i : Fin n) => Φ ω (u i.val))
        (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω =
          approxX n (ω, u) := by
    calc
      (∑ i : Fin n, (c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) *
          Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
            DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) =
          ∑ i : Fin n, (c * (n : ℝ)⁻¹) *
            ((h (u i.val) : ℝ) * Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
      _ = (c * (n : ℝ)⁻¹) * ∑ i : Fin n,
            ((h (u i.val) : ℝ) * Real.exp (γ * Φ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PX (fun ω => Φ ω (u i.val)))) := by rw [Finset.mul_sum]
      _ = c * ((n : ℝ)⁻¹ * ∑ i : Fin n, wx ω (u i.val)) := by ring
  have hformulaY (n : ℕ) (ω : ΩY) (u : ℕ → S) :
      DOZZ.finiteChaosMass PY (fun ω (i : Fin n) => Ψ ω (u i.val))
        (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω =
          approxY n (ω, u) := by
    calc
      (∑ i : Fin n, (c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) *
          Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
            DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) =
          ∑ i : Fin n, (c * (n : ℝ)⁻¹) *
            ((h (u i.val) : ℝ) * Real.exp (γ * Ψ ω (u i.val) - γ ^ 2 / 2 *
              DOZZ.gaussianVariance PY (fun ω => Ψ ω (u i.val)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
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
            DOZZ.gaussianCovariance PY (fun ω => Ψ ω (u i.val)) (fun ω => Ψ ω (u j.val)) := by
      simpa [Q, ρ] using hsample n
    filter_upwards [hsampleN] with u hu
    let Xn : ΩX → Fin n → ℝ := fun ω i => Φ ω (u i.val)
    let Yn : ΩY → Fin n → ℝ := fun ω i => Ψ ω (u i.val)
    have hXn : DOZZ.IsCenteredJointlyGaussian PX Xn := hΦ.2 n (fun i => u i.val)
    have hYn : DOZZ.IsCenteredJointlyGaussian PY Yn := hΨ.2 n (fun i => u i.val)
    have ha : ∀ i : Fin n, 0 ≤ c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ) := by
      intro i
      exact mul_nonneg (mul_nonneg (by positivity)
        (inv_nonneg.mpr (Nat.cast_nonneg n))) (NNReal.coe_nonneg _)
    have hfin := kahane_finite_laplace_lintegral_fintype PX PY Xn Yn hXn hYn
      (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) ha γ s hs
      (fun i j => hu i j)
    calc
      (∫⁻ ω, FX n (ω, u) ∂PX) =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
            DOZZ.finiteChaosMass PX Xn
              (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂PX := by
                apply lintegral_congr_ae
                exact ae_of_all _ fun ω => by
                  simpa [FX, Xn] using congrArg
                    (fun m => ENNReal.ofReal (Real.exp (-s * m)))
                    (hformulaX n ω u).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-s *
            DOZZ.finiteChaosMass PY Yn
              (fun i => c * (n : ℝ)⁻¹ * (h (u i.val) : ℝ)) γ ω)) ∂PY := hfin
      _ = ∫⁻ ω, FY n (ω, u) ∂PY := by
            apply lintegral_congr_ae
            exact ae_of_all _ fun ω => by
              simpa [FY, Yn] using congrArg
                (fun m => ENNReal.ofReal (Real.exp (-s * m)))
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
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
    have havg : 0 ≤ avgX n p := by
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum
    have happ : 0 ≤ approxX n p := by
      exact mul_nonneg (by positivity) havg
    have hexp : Real.exp (-s * approxX n p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) happ)
    simpa [FX] using ENNReal.ofReal_le_ofReal hexp
  have hboundY (n : ℕ) (p : ΩY × (ℕ → S)) : FY n p ≤ 1 := by
    have hsum : 0 ≤ ∑ i : Fin n, wy p.1 (p.2 i.val) := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)
    have havg : 0 ≤ avgY n p := by
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum
    have happ : 0 ≤ approxY n p := by
      exact mul_nonneg (by positivity) havg
    have hexp : Real.exp (-s * approxY n p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) happ)
    simpa [FY] using ENNReal.ofReal_le_ofReal hexp
  have hlimitXNested : ∀ᵐ ω ∂PX, ∀ᵐ u ∂Q,
      Tendsto (fun n => FX n (ω, u)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-s * limitX ω)))) := by
    have havgX' : ∀ᵐ ω ∂PX, ∀ᵐ u ∂Q,
        Tendsto (fun n => avgX n (ω, u)) atTop (𝓝 (∫ x, wx ω x ∂ρ)) := by
      simpa [avgX, Q, ρ] using (ae_empirical_average_tendsto PX ρ wx hwickX hintX)
    filter_upwards [havgX'] with ω havg
    filter_upwards [havg] with u havg'
    have hmass : Tendsto (fun n => approxX n (ω, u)) atTop (𝓝 (limitX ω)) := by
      simpa [approxX, limitX] using tendsto_const_nhds.mul havg'
    have harg : Tendsto (fun n => -s * approxX n (ω, u)) atTop (𝓝 (-s * limitX ω)) :=
      tendsto_const_nhds.mul hmass
    exact ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto (-s * limitX ω)).comp harg)
  have hlimitYNested : ∀ᵐ ω ∂PY, ∀ᵐ u ∂Q,
      Tendsto (fun n => FY n (ω, u)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-s * limitY ω)))) := by
    have havgY' : ∀ᵐ ω ∂PY, ∀ᵐ u ∂Q,
        Tendsto (fun n => avgY n (ω, u)) atTop (𝓝 (∫ x, wy ω x ∂ρ)) := by
      simpa [avgY, Q, ρ] using (ae_empirical_average_tendsto PY ρ wy hwickY hintY)
    filter_upwards [havgY'] with ω havg
    filter_upwards [havg] with u havg'
    have hmass : Tendsto (fun n => approxY n (ω, u)) atTop (𝓝 (limitY ω)) := by
      simpa [approxY, limitY] using tendsto_const_nhds.mul havg'
    have harg : Tendsto (fun n => -s * approxY n (ω, u)) atTop (𝓝 (-s * limitY ω)) :=
      tendsto_const_nhds.mul hmass
    exact ENNReal.tendsto_ofReal ((Real.continuous_exp.tendsto (-s * limitY ω)).comp harg)
  have hlimitMeasX : Measurable (fun p : ΩX × (ℕ → S) =>
      ENNReal.ofReal (Real.exp (-s * limitX p.1))) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul
        ((measurable_const.mul hρmeasX).comp measurable_fst)))
  have hlimitMeasY : Measurable (fun p : ΩY × (ℕ → S) =>
      ENNReal.ofReal (Real.exp (-s * limitY p.1))) := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (Real.measurable_exp.comp (measurable_const.mul
        ((measurable_const.mul hρmeasY).comp measurable_fst)))
  have hseqMeasX : ∀ n, Measurable (FX n) := hFXmeas
  have hseqMeasY : ∀ n, Measurable (FY n) := hFYmeas
  have hsetX : MeasurableSet {p : ΩX × (ℕ → S) |
      Tendsto (fun n => FX n p) atTop (𝓝 (ENNReal.ofReal (Real.exp (-s * limitX p.1))))} := by
    exact measurableSet_tendsto_fun hseqMeasX hlimitMeasX
  have hsetY : MeasurableSet {p : ΩY × (ℕ → S) |
      Tendsto (fun n => FY n p) atTop (𝓝 (ENNReal.ofReal (Real.exp (-s * limitY p.1))))} := by
    exact measurableSet_tendsto_fun (l := atTop) hseqMeasY hlimitMeasY
  have hlimitX : ∀ᵐ p ∂PX.prod Q,
      Tendsto (fun n => FX n p) atTop _ :=
    Measure.ae_prod_iff_ae_ae hsetX |>.2 hlimitXNested
  have hlimitY : ∀ᵐ p ∂PY.prod Q,
      Tendsto (fun n => FY n p) atTop _ :=
    Measure.ae_prod_iff_ae_ae hsetY |>.2 hlimitYNested
  have hlimitOrder := lintegral_order_of_laplace_approximants PX PY Q FX FY
    (fun ω => ENNReal.ofReal _)
    (fun ω => ENNReal.ofReal _)
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
      (by assumption)
    have hlimNonneg : 0 ≤ limitX ω := by
      apply mul_nonneg <;> positivity
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
      (by assumption)
    have hlimNonneg : 0 ≤ limitY ω := by
      apply mul_nonneg <;> positivity
    have htoReal : (DOZZ.fieldChaosMass PY Ψ (ν : Measure S) h γ ω).toReal = limitY ω := by
      rw [hfieldMass]
      exact ENNReal.toReal_ofReal hlimNonneg
    rw [htoReal]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal _ ∂PX := htargetX
    _ ≤ ∫⁻ ω, ENNReal.ofReal _ ∂PY := hlimitOrder
    _ = _ := htargetY.symm
section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Nonempty S] (P : Measure Ω) (Φ : Ω → S → ℝ)

theorem centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
    (ν : FiniteMeasure S) (h : S → ℝ≥0)
    (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ)
    (hzero : ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S) = 0) :
    ∀ ω, DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω = 0 := by
  have hbaseInt : Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) :=
    centeredGaussianField_bounded_weight_integrable ν h hh hhb
  have hbaseZero : (fun x => (h x : ℝ)) =ᵐ[(ν.normalize : Measure S)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => NNReal.coe_nonneg (h x)) hbaseInt).mp hzero
  intro ω
  let f : S → ℝ := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hzeroF : f =ᵐ[(ν.normalize : Measure S)] 0 := by
    filter_upwards [hbaseZero] with x hx
    aesop
  have hIntF : Integrable f (ν.normalize : Measure S) :=
    (integrable_congr hzeroF).mpr (integrable_const (0 : ℝ))
  rw [(fieldChaosMass_eq_ofReal_normalized_integral P Φ ν h γ ω hIntF)]
  have hfint : ∫ x, f x ∂(ν.normalize : Measure S) = 0 := by
    rw [integral_congr_ae hzeroF]
    simp
  aesop
section
variable (hΦ : DOZZ.IsCenteredGaussianField P Φ) (ν : FiniteMeasure S) (hν : ν ≠ 0) (h : S → ℝ≥0) (hh : Measurable h) (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ : ℝ) (hpos : 0 < ∫ x, (h x : ℝ) ∂(ν.normalize : Measure S))
include hΦ hν hh hhb γ hpos

theorem centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    :
    ∀ᵐ ω ∂P, 0 < DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω := by
  have hbaseInt : Integrable (fun x => (h x : ℝ)) (ν.normalize : Measure S) :=
    centeredGaussianField_bounded_weight_integrable ν h hh hhb
  have hbaseSupport : 0 < (ν.normalize : Measure S) (Function.support fun x => (h x : ℝ)) :=
    (integral_pos_iff_support_of_nonneg
     
      (fun x => NNReal.coe_nonneg (h x)) hbaseInt).mp hpos
  have : IsProbabilityMeasure P := (hΦ.2 0 Fin.elim0).1
  have hvar_nonneg (x : S) :
      0 ≤ DOZZ.gaussianVariance P (fun ω => Φ ω x) := by
    obtain ⟨v, _, _, hvar⟩ :=
      DOZZ.Proofs.coordinate_mean_variance P (fun ω (_ : Fin 1) => Φ ω x)
        (hΦ.2 1 (fun _ => x)) (0 : Fin 1)
    simp_all
  have hint := centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ
  filter_upwards [hint] with ω hω
  let f : S → ℝ := fun x => (h x : ℝ) * Real.exp
    (γ * Φ ω x - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Φ ω x))
  have hf_nonneg (x : S) : 0 ≤ f x :=
    by positivity
  have hfsupport : Function.support f = Function.support fun x => (h x : ℝ) := by
    aesop
  have hfpos : 0 < ∫ x, f x ∂(ν.normalize : Measure S) := by
    rw [integral_pos_iff_support_of_nonneg hf_nonneg hω, hfsupport]
    exact hbaseSupport
  have hrepresentation := fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω (by assumption)
  have hmasspos : 0 < (ν.mass : ℝ) := by
    have hmassne : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
    positivity
  rw [hrepresentation]
  exact ENNReal.ofReal_pos.mpr (mul_pos hmasspos hfpos)

theorem fieldChaosMass_eq_ofReal_modified_toReal_ae
    :
    let M := fun ω => DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω
    let m := fun ω => if (M ω).toReal = 0 then 1 else (M ω).toReal
    ∀ᵐ ω ∂P, M ω = ENNReal.ofReal (m ω) := by
  dsimp
  have hint := centeredGaussianField_ae_integrable_weighted_wick
    P Φ hΦ ν h hh hhb γ
  have hmasspos := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    P Φ hΦ ν hν h hh hhb γ hpos
  filter_upwards [hint, hmasspos] with ω hω hposω
  have hrepresentation := fieldChaosMass_eq_ofReal_normalized_integral
    P Φ ν h γ ω (by assumption)
  have hfinite : DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω ≠ ∞ := by
    rw [hrepresentation]
    exact ENNReal.ofReal_ne_top
  have htoRealPos : 0 < (DOZZ.fieldChaosMass P Φ (ν : Measure S) h γ ω).toReal :=
    ENNReal.toReal_pos hposω.ne' hfinite
  simp [ne_of_gt htoRealPos, hfinite]

end

end
section
variable {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]

theorem kahane_field_power_nonpos
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
  classical
  have hPYzero := hΨ.2 0 (fun i : Fin 0 => Fin.elim0 i)
  have : IsProbabilityMeasure PX := (hΦ.2 0 (fun i : Fin 0 => Fin.elim0 i)).1
  have : IsProbabilityMeasure PY := hPYzero.1
  by_cases hp0 : p = 0
  · simp_all
  have hpneg := lt_of_le_of_ne hp hp0
  by_cases hνzero : ν = 0
  · have hmassX (ω : ΩX) : DOZZ.fieldChaosMass PX Φ ν h γ ω = 0 := by
      simp [DOZZ.fieldChaosMass, hνzero]
    have hmassY (ω : ΩY) : DOZZ.fieldChaosMass PY Ψ ν h γ ω = 0 := by
      simp [DOZZ.fieldChaosMass, hνzero]
    simp_all
  let νf : FiniteMeasure S := ⟨ν, inferInstance⟩
  have hνf : νf ≠ 0 := by
    intro hzero
    apply hνzero
    simpa [νf] using (congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) hzero)
  have hS : Nonempty S := by
    have hUniv := Measure.measure_univ_ne_zero.mpr hνzero
    obtain ⟨x, _⟩ := nonempty_of_measure_ne_zero hUniv
    exact ⟨x⟩
  have : Nonempty S := hS
  let ρ : Measure S := νf.normalize
  have hρprob : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have : IsProbabilityMeasure ρ := hρprob
  let α : ℝ := ∫ x, (h x) ∂ρ
  have hαnonneg : 0 ≤ α := by
    dsimp [α]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => NNReal.coe_nonneg (h x))
  by_cases hα0 : α = 0
  · have hmassX := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PX Φ νf h hh hhb γ (by assumption)
    have hmassY := centeredGaussianField_fieldChaosMass_eq_zero_of_zero_weight_integral
      PY Ψ νf h hh hhb γ (by assumption)
    aesop
  have hαpos := lt_of_le_of_ne hαnonneg (Ne.symm hα0)
  have hcov' : ∀ᵐ xy ∂(νf : Measure S).prod νf,
      DOZZ.gaussianCovariance PX (fun ω => Φ ω xy.1) (fun ω => Φ ω xy.2) ≤
        DOZZ.gaussianCovariance PY (fun ω => Ψ ω xy.1) (fun ω => Ψ ω xy.2) := by
    filter_upwards [hcov] with xy hxy
    simpa [DOZZ.gaussianCovariance] using hxy
  have hdiag' : ∀ᵐ x ∂(νf : Measure S),
      DOZZ.gaussianVariance PX (fun ω => Φ ω x) ≤
        DOZZ.gaussianVariance PY (fun ω => Ψ ω x) := by
    filter_upwards [hdiag] with x hx
    simpa [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, pow_two] using hx
  let MX : ΩX → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass PX Φ ν h γ ω
  let MY : ΩY → ℝ≥0∞ := fun ω => DOZZ.fieldChaosMass PY Ψ ν h γ ω
  let mX : ΩX → ℝ := fun ω => if (MX ω).toReal = 0 then 1 else (MX ω).toReal
  let mY : ΩY → ℝ := fun ω => if (MY ω).toReal = 0 then 1 else (MY ω).toReal
  have hmassMeasX := centeredGaussianField_fieldChaosMass_measurable PX Φ hΦ ν h hh γ
  have hmassMeasY := centeredGaussianField_fieldChaosMass_measurable PY Ψ hΨ ν h hh γ
  have hmXMeas : Measurable mX := by
    apply Measurable.ite
      (measurableSet_eq_fun hmassMeasX.ennreal_toReal measurable_const)
    · exact measurable_const
    · exact hmassMeasX.ennreal_toReal
  have hmYMeas : Measurable mY := by
    apply Measurable.ite
      (measurableSet_eq_fun hmassMeasY.ennreal_toReal measurable_const)
    · exact measurable_const
    · exact hmassMeasY.ennreal_toReal
  have hmX : ∀ ω, 0 < mX ω := by
    intro ω
    dsimp [mX]
    split_ifs with hzero
    · norm_num
    · positivity
  have hmY : ∀ ω, 0 < mY ω := by
    intro ω
    dsimp [mY]
    split_ifs with hzero
    · norm_num
    · positivity
  have hintX := centeredGaussianField_ae_integrable_weighted_wick PX Φ hΦ νf h hh hhb γ
  have hintY := centeredGaussianField_ae_integrable_weighted_wick PY Ψ hΨ νf h hh hhb γ
  have hmassPosX := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    PX Φ hΦ νf hνf h hh hhb γ (by assumption)
  have hmassPosY := centeredGaussianField_fieldChaosMass_pos_ae_of_pos_weight_integral
    PY Ψ hΨ νf hνf h hh hhb γ (by assumption)
  have hmassEqX : ∀ᵐ ω ∂PX, MX ω = ENNReal.ofReal (mX ω) := by
    change ∀ᵐ ω ∂PX,
      DOZZ.fieldChaosMass PX Φ ν h γ ω = ENNReal.ofReal
        (if (DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal = 0 then 1 else
          (DOZZ.fieldChaosMass PX Φ ν h γ ω).toReal)
    exact fieldChaosMass_eq_ofReal_modified_toReal_ae
      PX Φ hΦ νf hνf h hh hhb γ (by assumption)
  have hmassEqY : ∀ᵐ ω ∂PY, MY ω = ENNReal.ofReal (mY ω) := by
    change ∀ᵐ ω ∂PY,
      DOZZ.fieldChaosMass PY Ψ ν h γ ω = ENNReal.ofReal
        (if (DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal = 0 then 1 else
          (DOZZ.fieldChaosMass PY Ψ ν h γ ω).toReal)
    exact fieldChaosMass_eq_ofReal_modified_toReal_ae
      PY Ψ hΨ νf hνf h hh hhb γ (by assumption)
  have htoRealEqX : ∀ᵐ ω ∂PX, (MX ω).toReal = mX ω := by
    filter_upwards [hmassEqX] with ω hω
    rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmX ω))]
  have htoRealEqY : ∀ᵐ ω ∂PY, (MY ω).toReal = mY ω := by
    filter_upwards [hmassEqY] with ω hω
    rw [hω, ENNReal.toReal_ofReal (le_of_lt (hmY ω))]
  have hLaplace (t : ℝ) (ht : 0 ≤ t) :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mX ω)) ∂PX ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mY ω)) ∂PY := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (MX ω).toReal)) ∂PX := by
        apply lintegral_congr_ae
        filter_upwards [htoRealEqX] with ω hω
        rw [hω]
      _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (MY ω).toReal)) ∂PY := by
        simpa [νf, MX, MY] using DOZZ.Proofs.kahane_field_laplace_of_nonzero_finite_measure
          PX PY Φ Ψ hΦ hΨ νf hνf h hh hhb γ t ht hcov' hdiag'
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * mY ω)) ∂PY := by
        apply lintegral_congr_ae
        filter_upwards [htoRealEqY] with ω hω
        rw [hω]
  have hMellinX := finite_rpow_neg_lintegral_eq_weighted_laplace PX mX hmX
    hmXMeas.aemeasurable (-p) (neg_pos.mpr hpneg)
  have hMellinY := finite_rpow_neg_lintegral_eq_weighted_laplace PY mY hmY
    hmYMeas.aemeasurable (-p) (neg_pos.mpr hpneg)
  have hMellinCompare :
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (-p - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume ≤
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (t ^ (-p - 1)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hXexp : (fun ω => ENNReal.ofReal (Real.exp (-t * mX ω))) =
        fun ω => ENNReal.ofReal (Real.exp (-(mX ω * t))) := by
      funext ω
      congr 2
      ring
    have hYexp : (fun ω => ENNReal.ofReal (Real.exp (-t * mY ω))) =
        fun ω => ENNReal.ofReal (Real.exp (-(mY ω * t))) := by
      funext ω
      congr 2
      ring
    gcongr
    rw [← hXexp, ← hYexp]
    exact hLaplace t ht.le
  have hMomentX :
      ∫⁻ ω, MX ω ^ p ∂PX = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mX ω)) p ∂PX := by
    apply lintegral_congr_ae
    filter_upwards [hmassEqX] with ω hω
    rw [hω]
    rfl
  have hMomentY :
      ∫⁻ ω, MY ω ^ p ∂PY = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (mY ω)) p ∂PY := by
    apply lintegral_congr_ae
    filter_upwards [hmassEqY] with ω hω
    rw [hω]
    rfl
  calc
    _ = ∫⁻ ω, ENNReal.rpow _ p ∂PX := hMomentX
    _ = ENNReal.ofReal _ *
          ∫⁻ t in Set.Ioi 0, ENNReal.ofReal _ *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mX ω * t))) ∂PX) ∂volume := by
          simpa using hMellinX
    _ ≤ ENNReal.ofReal _ *
          ∫⁻ t in Set.Ioi 0, ENNReal.ofReal _ *
            (∫⁻ ω, ENNReal.ofReal (Real.exp (-(mY ω * t))) ∂PY) ∂volume := mul_le_mul_of_nonneg_left hMellinCompare (by positivity)
    _ = ∫⁻ ω, ENNReal.rpow _ p ∂PY := by
          symm
          simpa using hMellinY
    _ = _ := hMomentY.symm

end


end DOZZ.Proofs
