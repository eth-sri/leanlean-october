/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.CircleScale
public import DOZZ.GMC.Moments.ChaosLawFDDNoAux
public import DOZZ.GMC.FiniteChaosMean
public import DOZZ.GMC.CircleWickDensity

/-! Exact affine scaling in law for finite-cutoff Wick integrals on a compact spatial chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- The variance of a circle average is a measurable function of its center. -/
theorem circleAverage_variance_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Xc : Ω → ℂ → ℝ → ℝ) (hmeas : ∀ r, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r))
    (r : ℝ) :
    Measurable (fun x => gaussianVariance P (fun ω => Xc ω x r)) := by
  simpa only [gaussianVariance, gaussianCovariance, pow_two] using measurable_secondMoment P (hmeas r)

/-- A circle average has its centered Gaussian law with the variance computed by the second-moment
definition `DOZZ.gaussianVariance`. The accompanying nonnegativity is useful when converting that
variance to an `NNReal` normalization. -/
theorem circleAverage_gaussian_law_and_variance_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (x : ℂ) (r : ℝ) :
    HasLaw (fun ω => Xc ω x r)
        (gaussianReal 0 (gaussianVariance P (fun ω => Xc ω x r)).toNNReal) P ∧
      0 ≤ gaussianVariance P (fun ω => Xc ω x r) := by
  let Z : Ω → Fin 1 → ℝ := fun ω _ => Xc ω x r
  have hZ : IsCenteredJointlyGaussian P Z := by
    simpa [Z] using circleAverage_finite_family_jointly_gaussian P X hX Xc hXc
      (fun _ : Fin 1 => (x, r))
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ 0
  have hv : 0 ≤ gaussianVariance P (fun ω => Xc ω x r) := by
    have hvar' : gaussianVariance P (fun ω => Xc ω x r) = (v : ℝ) := by
      simpa [Z] using hvar
    rw [hvar']
    positivity
  have hvEq : v = (gaussianVariance P (fun ω => Xc ω x r)).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ hv]
    simpa [Z] using hvar.symm
  have hmeas : AEMeasurable (fun ω => Xc ω x r) P := (hXc.1 r).comp (measurable_id.prodMk measurable_const) |>.aemeasurable
  refine ⟨⟨hmeas, ?_⟩, hv⟩
  change Measure.map (fun ω => Z ω 0) P = _
  rw [hmap, hvEq]

noncomputable def circleWick {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) (x : ℂ) : ℝ :=
  Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r))

theorem measurable_circleWick {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Xc : Ω → ℂ → ℝ → ℝ}
    (hXc : ∀ r, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) (γ r : ℝ) :
    Measurable (fun p : Ω × ℂ => circleWick P Xc γ r p.1 p.2) :=
  Real.measurable_exp.comp ((measurable_const.mul (hXc r)).sub
    (measurable_const.mul ((circleAverage_variance_measurable Xc hXc r).comp measurable_snd)))

theorem measurable_circleWick_vector {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} [IsProbabilityMeasure P] {Xc : Ω → ℂ → ℝ → ℝ}
    (hXc : ∀ r, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) {z : S → ℂ} (hz : Measurable z)
    {ν : Measure S} [SFinite ν] {m : ℕ} {f : Fin m → S → ℝ} (hf : ∀ j, Measurable (f j))
    (γ r : ℝ) : Measurable (fun ω j => ∫ x, f j x * circleWick P Xc γ r ω (z x) ∂ν) :=
  measurable_pi_iff.mpr fun j => (((hf j).comp measurable_snd).mul
    ((measurable_circleWick (P := P) hXc γ r).comp (measurable_fst.prodMk
      (hz.comp measurable_snd)))).stronglyMeasurable.integral_prod_right'.measurable

/-- Finite-cutoff affine scaling for several weighted chaos integrals. The covariance identity for
circle averages supplies the common Gaussian scalar, and `ChaosLawFDD` transfers its finite
dimensional law to the integrals. -/
theorem circleAverage_affine_scaled_wick_integral_law
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {m : ℕ} (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hXc : IsCircleAverage P X Xc)
    (ν : Measure S) [IsProbabilityMeasure ν]
    {a : ℂ} {c r γ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (z : S → ℂ) (hz : Measurable z) (hbase : ∀ x, ‖z x‖ + Real.exp (-r) ≤ 1)
    (hscaled : ∀ x, ‖a + c * z x‖ + Real.exp (-(r - Real.log c)) ≤ 1)
    (weight : Fin m → S → ℝ)
    (hweight : ∀ j, Measurable (weight j))
    (hweight_nonneg : ∀ j x, 0 ≤ weight j x)
    (hweight_int : ∀ j, Integrable (weight j) ν) :
    IdentDistrib
      (fun ω j => ∫ x, weight j x * circleWick P Xc γ (r - Real.log c) ω (a + c * z x) ∂ν)
      (fun p : Ω × ℝ => fun j => Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) *
        ∫ x, weight j x * circleWick P Xc γ r p.1 (z x) ∂ν)
      P (P.prod (gaussianReal 0 ⟨-Real.log c, neg_nonneg.mpr (Real.log_nonpos hc.le hc₁)⟩)) := by
  classical
  let σ  := -Real.log c
  let varianceBase  := fun x =>
    (gaussianVariance P (fun ω => Xc ω (z x) r)).toNNReal
  let varianceTotal  := fun x =>
    (gaussianVariance P (fun ω => Xc ω (a + c * z x) (r - Real.log c))).toNNReal
  let W : Ω × ℝ → ℝ := Prod.snd
  let G  := gaussianReal 0 ⟨-Real.log c,
    neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc₁)⟩
  let P'  := P.prod G
  let X'  := fun ω x => Xc ω (a + c * z x) (r - Real.log c)
  let Y : Ω × ℝ → S → ℝ := fun p x => Xc p.1 (z x) r
  let := hX.1
  let : IsProbabilityMeasure G := ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have hvarianceBase := (measurable_real_toNNReal.comp
      (circleAverage_variance_measurable (P := P) Xc hXc.1 r)).comp
        hz
  have hvarianceTotal := (measurable_real_toNNReal.comp
      (circleAverage_variance_measurable (P := P) Xc hXc.1 (r - Real.log c))).comp
        (by fun_prop : Measurable (fun x : S => a + c * z x))
  have hX' : Measurable (fun p : Ω × S => X' p.1 p.2) := by
    dsimp [X']
    exact (hXc.1 (r - Real.log c)).comp (by fun_prop :
      Measurable (fun p : Ω × S => (p.1, a + c * z p.2)))
  have hY : Measurable (fun p : (Ω × ℝ) × S => Y p.1 p.2) := by
    dsimp [Y]
    exact (hXc.1 r).comp (by fun_prop :
      Measurable (fun p : (Ω × ℝ) × S => (p.1.1, z p.2)))
  have hW : Measurable W := measurable_snd
  have hXlaw (x : S) : HasLaw (fun ω => X' ω x)
      (gaussianReal 0 (varianceTotal x)) P := by
    simpa [X', varianceTotal] using
      (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc
        (a + c * z x) (r - Real.log c)).1
  have hYlaw (x : S) : HasLaw (fun p : Ω × ℝ => Y p x)
      (gaussianReal 0 (varianceBase x)) P' :=
    (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc (z x) r).1.comp
      measurePreserving_fst.hasLaw
  have hb (x : S) : (varianceBase x : ℝ) = gaussianVariance P (fun ω => Xc ω (z x) r) :=
    Real.coe_toNNReal _ (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc (z x) r).2
  have ht (x : S) : (varianceTotal x : ℝ) = gaussianVariance P (fun ω => X' ω x) :=
    Real.coe_toNNReal _ (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc
      (a + c * z x) (r - Real.log c)).2
  have hCov (y : ℂ) (s : ℝ) : gaussianVariance P (fun ω => Xc ω y s) =
      ProbabilityTheory.covariance (fun ω => Xc ω y s) (fun ω => Xc ω y s) P := by
    simp [gaussianVariance, gaussianCovariance, ProbabilityTheory.covariance,
      (circleAverage_isGaussianProcess P X Xc hX hXc).2 y s]
  have hVariance (x : S) : (varianceBase x : ℝ) + σ = (varianceTotal x : ℝ) := by
    rw [hb, ht]
    dsimp only [X']
    rw [hCov, hCov, circleAverage_covariance_affine_scale P X Xc hX hXc hc
      (z x) (z x) r r (hbase x) (hbase x) (hscaled x) (hscaled x)]
    rfl
  have hFDD : ∀ (n : ℕ) (xs : Fin n → S),
      Measure.map (fun ω i => X' ω (xs i)) P =
        Measure.map (fun p : Ω × ℝ => fun i => Y p (xs i) + W p) P' := by
    intro n xs
    simpa [X', Y, W, P', G] using
      (circleAverage_affine_scaled_fdd_law P X Xc hX hXc hc hc₁
        (fun i => z (xs i)) (fun i => r) (fun i => hbase (xs i))
        (fun i => hscaled (xs i)))
  have hShiftLaw (x : S) : HasLaw (fun p : Ω × ℝ => Y p x + W p)
      (gaussianReal 0 (varianceTotal x)) P' := by
    have h := congrArg (Measure.map (fun v : Fin 1 → ℝ => v 0)) (hFDD 1 fun _ => x)
    have he : Measurable (fun v : Fin 1 → ℝ => v 0) := measurable_pi_apply 0
    rw [Measure.map_map he (by fun_prop), Measure.map_map he (by fun_prop)] at h
    exact ⟨(by fun_prop : Measurable (fun p => Y p x + W p)).aemeasurable,
      h.symm.trans (hXlaw x).map_eq⟩
  have hm₁ := measurable_circleWick_vector (P := P) (ν := ν) hXc.1
    (z := fun x => a + c * z x) (by fun_prop) hweight γ (r - Real.log c)
  have hm₂ := measurable_circleWick_vector (P := P) (ν := ν) hXc.1 hz hweight γ r
  have hfac : Measurable (fun p : Ω × ℝ => Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c))) := by
    fun_prop
  refine ⟨hm₁.aemeasurable, (measurable_pi_iff.mpr fun j =>
    hfac.mul (((measurable_pi_apply j).comp hm₂).comp measurable_fst)).aemeasurable, ?_⟩
  simpa only [circleWick, ht, hb, σ, W, P', G, X', Y] using
    (chaosLawFDD_independent_scalar_shift ν X' Y W varianceBase varianceTotal σ γ
      weight hX' hY hW hvarianceBase hvarianceTotal hweight hweight_nonneg hweight_int
      hVariance hXlaw hYlaw hShiftLaw hFDD)

end DOZZ.Proofs
