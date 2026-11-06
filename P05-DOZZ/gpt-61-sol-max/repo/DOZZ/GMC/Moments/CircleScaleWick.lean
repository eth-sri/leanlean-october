/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.CircleScale
public import DOZZ.GMC.Moments.ChaosLawFDDNoAux
public import DOZZ.GMC.FiniteChaosMean

/-! Exact affine scaling in law for finite-cutoff Wick integrals on a compact spatial chart. -/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- The variance of a circle average is a measurable function of its center. -/
theorem circleAverage_variance_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Xc : Ω → ℂ → ℝ → ℝ) (hmeas : ∀ r, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r))
    (r : ℝ) :
    Measurable (fun x => gaussianVariance P (fun ω => Xc ω x r)) := by
  have hfield  := hmeas r
  have hswap  :=
    hfield.comp measurable_swap
  have hsquare  :=
    hswap.pow_const 2
  have hvar : Measurable (fun x : ℂ => ∫ ω, Xc ω x r ^ 2 ∂P) :=
    hsquare.stronglyMeasurable.integral_prod_right.measurable
  have heq : (fun x : ℂ => gaussianVariance P (fun ω => Xc ω x r)) =
      fun x => ∫ ω, Xc ω x r ^ 2 ∂P := by
    noncomm_ring
  rw [heq]
  exact hvar

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
  have hZ : IsCenteredJointlyGaussian P Z := id (circleAverage_finite_family_jointly_gaussian P X hX Xc hXc fun x_1 => (x, r))
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ 0
  have hv : 0 ≤ gaussianVariance P (fun ω => Xc ω x r) := by
    continuity
  have hvEq : v = (gaussianVariance P (fun ω => Xc ω x r)).toNNReal := by
    continuity
  have hmeas : AEMeasurable (fun ω => Xc ω x r) P := (hXc.1 r).comp (measurable_id.prodMk measurable_const) |>.aemeasurable
  refine ⟨⟨hmeas, ?_⟩, hv⟩
  continuity

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
    let σ : ℝ := -Real.log c
    let varianceBase : S → ℝ≥0 := fun x =>
      (gaussianVariance P (fun ω => Xc ω (z x) r)).toNNReal
    let varianceTotal : S → ℝ≥0 := fun x =>
      (gaussianVariance P (fun ω => Xc ω (a + c * z x) (r - Real.log c))).toNNReal
    let W : Ω × ℝ → ℝ := Prod.snd
    Measure.map (fun ω => fun j => ∫ x, weight j x * Real.exp
        (γ * Xc ω (a + c * z x) (r - Real.log c) - γ ^ 2 / 2 *
          (varianceTotal x : ℝ)) ∂ν) P =
      Measure.map (fun p : Ω × ℝ => fun j =>
        Real.exp (γ * W p - γ ^ 2 / 2 * σ) *
          ∫ x, weight j x * Real.exp
            (γ * Xc p.1 (z x) r - γ ^ 2 / 2 * (varianceBase x : ℝ)) ∂ν)
        (P.prod (gaussianReal 0 ⟨-Real.log c,
          neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc₁)⟩)) := by
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
  have hP  := hX.1
  let  := hP
  have hG : IsProbabilityMeasure (gaussianReal 0 ⟨-Real.log c,
      neg_nonneg.mpr (Real.log_nonpos (le_of_lt hc) hc₁)⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  let : IsProbabilityMeasure G := hG
  let : IsProbabilityMeasure P' := by infer_instance
  have hvarianceBase  := (measurable_real_toNNReal.comp
      (circleAverage_variance_measurable (P := P) Xc hXc.1 r)).comp
        hz
  have hvarianceTotal  := (measurable_real_toNNReal.comp
      (circleAverage_variance_measurable (P := P) Xc hXc.1 (r - Real.log c))).comp
        (by fun_prop : Measurable (fun x : S => a + c * z x))
  have hX' : Measurable (fun p : Ω × S => X' p.1 p.2) := (hXc.1 (r - Real.log c)).comp (by fun_prop :
      Measurable (fun p : Ω × S => (p.1, a + c * z p.2)))
  have hY : Measurable (fun p : (Ω × ℝ) × S => Y p.1 p.2) := (hXc.1 r).comp (by fun_prop :
      Measurable (fun p : (Ω × ℝ) × S => (p.1.1, z p.2)))
  have hW : Measurable W := measurable_snd
  have hXlaw (x : S) : HasLaw (fun ω => X' ω x)
      (gaussianReal 0 (varianceTotal x)) P := (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc
        (a + c * z x) (r - Real.log c)).1
  have hYbaseLaw (x : S) : HasLaw (fun ω => Xc ω (z x) r)
      (gaussianReal 0 (varianceBase x)) P := (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc (z x) r).1
  have hYlaw (x : S) : HasLaw (fun p : Ω × ℝ => Y p x)
      (gaussianReal 0 (varianceBase x)) P' := by
    have hmap : Measure.map (fun p : Ω × ℝ => Y p x) P' =
        Measure.map (fun ω => Xc ω (z x) r) P := by
      have hbaseMeas : Measurable (fun ω : Ω => Xc ω (z x) r) := (hXc.1 r).comp (measurable_id.prodMk measurable_const)
      rw [show (fun p : Ω × ℝ => Y p x) =
        (fun ω => Xc ω (z x) r) ∘ Prod.fst by rfl,
        ← Measure.map_map hbaseMeas measurable_fst,
        measurePreserving_fst.map_eq]
    exact ⟨((hXc.1 r).comp (measurable_fst.prodMk measurable_const)).aemeasurable, by
      rw [hmap, (hYbaseLaw x).map_eq]
    ⟩
  have hbaseVariance (x : S) : 0 ≤ gaussianVariance P (fun ω => Xc ω (z x) r) :=
    (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc (z x) r).2
  have htotalVariance (x : S) : 0 ≤ gaussianVariance P
      (fun ω => Xc ω (a + c * z x) (r - Real.log c)) :=
    (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc
      (a + c * z x) (r - Real.log c)).2
  have hVariance (x : S) : (varianceBase x : ℝ) + σ = (varianceTotal x : ℝ) := by
    have hbaseVar  := Real.coe_toNNReal _ (hbaseVariance x)
    have htotalVar  := Real.coe_toNNReal _ (htotalVariance x)
    have hmean := (circleAverage_isGaussianProcess P X Xc hX hXc).2
    have hbaseCov : gaussianVariance P (fun ω => Xc ω (z x) r) =
        ProbabilityTheory.covariance (fun ω => Xc ω (z x) r)
          (fun ω => Xc ω (z x) r) P := by
      simp [gaussianVariance, gaussianCovariance, ProbabilityTheory.covariance,
        hmean (z x) r]
    have htotalCov : gaussianVariance P
        (fun ω => Xc ω (a + c * z x) (r - Real.log c)) =
        ProbabilityTheory.covariance (fun ω => Xc ω (a + c * z x) (r - Real.log c))
          (fun ω => Xc ω (a + c * z x) (r - Real.log c)) P := by
      simp [gaussianVariance, gaussianCovariance, ProbabilityTheory.covariance,
        hmean (a + c * z x) (r - Real.log c)]
    have hcov := circleAverage_covariance_affine_scale P X Xc hX hXc hc
      (z x) (z x) r r (hbase x) (hbase x) (hscaled x) (hscaled x)
    grind
  have hFDD : ∀ (n : ℕ) (xs : Fin n → S),
      Measure.map (fun ω i => X' ω (xs i)) P =
        Measure.map (fun p : Ω × ℝ => fun i => Y p (xs i) + W p) P' := by
    intro n xs
    exact (circleAverage_affine_scaled_fdd_law P X Xc hX hXc hc hc₁
        (fun i => z (xs i)) (fun i => r) (fun i => hbase (xs i))
        (fun i => hscaled (xs i)))
  have hShiftLaw (x : S) : HasLaw (fun p : Ω × ℝ => Y p x + W p)
      (gaussianReal 0 (varianceTotal x)) P' := by
    have hvecMeas : Measurable (fun ω : Ω => fun _ : Fin 1 => X' ω x) := by
      fun_prop (disch := positivity)
    have hvecMeas' : Measurable (fun p : Ω × ℝ => fun _ : Fin 1 => Y p x + W p) := by
      fun_prop (disch := positivity)
    have hproj : Measurable (fun v : Fin 1 → ℝ => v 0) := measurable_pi_apply 0
    have hleft : Measure.map (fun ω => X' ω x) P =
        (Measure.map (fun ω => fun _ : Fin 1 => X' ω x) P).map
          (fun v : Fin 1 → ℝ => v 0) := by
      change Measure.map ((fun v : Fin 1 → ℝ => v 0) ∘
        (fun ω => fun _ : Fin 1 => X' ω x)) P = _
      rw [← Measure.map_map hproj hvecMeas]
    have hright : Measure.map (fun p : Ω × ℝ => Y p x + W p) P' =
        (Measure.map (fun p : Ω × ℝ => fun _ : Fin 1 => Y p x + W p) P').map
          (fun v : Fin 1 → ℝ => v 0) := by
      change Measure.map ((fun v : Fin 1 → ℝ => v 0) ∘
        (fun p : Ω × ℝ => fun _ : Fin 1 => Y p x + W p)) P' = _
      rw [← Measure.map_map hproj hvecMeas']
    have hmap : Measure.map (fun ω => X' ω x) P =
        Measure.map (fun p : Ω × ℝ => Y p x + W p) P' := by
      calc
        _ = (Measure.map (fun ω => fun _ : Fin 1 => X' ω x) P).map
            (fun v : Fin 1 → ℝ => v 0) := hleft
        _ = (Measure.map (fun p : Ω × ℝ => fun _ : Fin 1 => Y p x + W p) P').map
            (fun v : Fin 1 → ℝ => v 0) := congrArg
              (fun μ => μ.map (fun v : Fin 1 → ℝ => v 0)) (hFDD 1 (fun _ => x))
        _ = _ := hright.symm
    exact ⟨((hY.comp (measurable_id.prodMk measurable_const)).add hW).aemeasurable,
      by calc
        Measure.map (fun p : Ω × ℝ => Y p x + W p) P' =
            Measure.map (fun ω => X' ω x) P := hmap.symm
        _ = gaussianReal 0 (varianceTotal x) := (hXlaw x).map_eq⟩
  exact (chaosLawFDD_independent_scalar_shift ν X' Y W varianceBase varianceTotal σ γ
      weight hX' hY hW hvarianceBase hvarianceTotal hweight hweight_nonneg hweight_int
      hVariance hXlaw hYlaw hShiftLaw hFDD)

end DOZZ.Proofs
