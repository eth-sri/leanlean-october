/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.CircleAverageL2Geometry
public import DOZZ.GFFStructure.CircleVersion

/-!
# Joint circle-average versions

The canonical L² family has Gaussian increments with the same logarithmic-potential bounds as circle
averages. Spatial Kolmogorov modifications at each fixed logarithmic radius, followed by raw-sigma
gluing, produce the jointly measurable circle-average witness (`DOZZ.IsCircleAverage`) on the
original field space.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (Y : (ℂ × ℝ) → Ω → ℝ)
  (hmem : ∀ p, MemLp (Y p) 2 P)
  (hcov : ∀ p q, covariance (Y p) (Y q) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
  (x y : ℂ)
include Ω hmem hcov

/-- Variance of an increment of the canonical L² circle family. -/
theorem circleL2_increment_variance_formula (r s : ℝ) :
    variance (fun ω => Y (x, r) ω - Y (y, s) ω) P = r + s +
      (∫ z, Real.log (max (Real.exp (-r)) ‖x-z‖) ∂circleMeasure y s) +
      (∫ z, Real.log (max (Real.exp (-s)) ‖y-z‖) ∂circleMeasure x r) := by
  let p : ℂ × ℝ := (x, r)
  let q : ℂ × ℝ := (y, s)
  let Lp := ∫ z, Real.log (normPlus z) ∂circleMeasure x r
  let Lq := ∫ z, Real.log (normPlus z) ∂circleMeasure y s
  let A := ∫ z, Real.log (max (Real.exp (-r)) ‖x-z‖) ∂circleMeasure y s
  let B := ∫ z, Real.log (max (Real.exp (-s)) ‖y-z‖) ∂circleMeasure x r
  have hdiagP : covariance (Y p) (Y p) P = r + 2 * Lp := by
    calc
      covariance (Y p) (Y p) P = circleSelfEnergy x r := by
        simpa only [circleSelfEnergy] using hcov p p
      _ = r + 2 * Lp := by simpa only [Lp] using circleSelfEnergy_eq x r
  have hdiagQ : covariance (Y q) (Y q) P = s + 2 * Lq := by
    calc
      covariance (Y q) (Y q) P = circleSelfEnergy y s := by
        simpa only [circleSelfEnergy] using hcov q q
      _ = s + 2 * Lq := by simpa only [Lq] using circleSelfEnergy_eq y s
  have hcrossPQ : covariance (Y p) (Y q) P = -A + Lq + Lp := by
    calc
      covariance (Y p) (Y q) P =
          ∫ z, ∫ w, gffKernel z w ∂circleMeasure x r ∂circleMeasure y s := hcov p q
      _ = -A + Lq + Lp := by
        simpa only [A, Lp, Lq] using
          (integral_integral_gffKernel_eq_logmax y x s r)
  have hcrossQP : covariance (Y q) (Y p) P = -B + Lp + Lq := by
    calc
      covariance (Y q) (Y p) P =
          ∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure x r := hcov q p
      _ = -B + Lp + Lq := by
        simpa only [B, Lp, Lq] using
          (integral_integral_gffKernel_eq_logmax x y r s)
  have hdiff : AEMeasurable (fun ω => Y p ω - Y q ω) P :=
    (hmem p).aemeasurable.sub (hmem q).aemeasurable
  have hExpand := covariance_fun_sub_fun_sub (hmem p) (hmem q) (hmem p) (hmem q)
  have hVariance : variance (fun ω => Y p ω - Y q ω) P =
      covariance (Y p) (Y p) P - covariance (Y p) (Y q) P -
        covariance (Y q) (Y p) P + covariance (Y q) (Y q) P := by
    rw [← covariance_self hdiff, hExpand]
  rw [show (fun ω => Y (x, r) ω - Y (y, s) ω) = fun ω => Y p ω - Y q ω by rfl,
    hVariance, hdiagP, hcrossPQ, hcrossQP, hdiagQ]
  dsimp [A, B, Lp, Lq]
  ring

/-- Same-radius circle increments have variance at most a constant times center distance. -/
theorem circleL2_increment_variance_le_center (r : ℝ) :
    variance (fun ω => Y (x, r) ω - Y (y, r) ω) P ≤
      2 * Real.exp r * ‖x-y‖ := by
  let A := ∫ z, Real.log (max (Real.exp (-r)) ‖x-z‖) ∂circleMeasure y r
  let B := ∫ z, Real.log (max (Real.exp (-r)) ‖y-z‖) ∂circleMeasure x r
  rw [circleL2_increment_variance_formula Y hmem hcov x y r r]
  have hA := integral_circle_logmax_sub_le y x r r
  have hB := integral_circle_logmax_sub_le x y r r
  have hA' : A + r ≤ ‖x-y‖ / Real.exp (-r) := by
    dsimp [A] at hA ⊢
    simpa only [Real.log_exp, sub_neg_eq_add, abs_zero, sub_self, add_zero,
      norm_sub_rev] using hA
  have hB' : B + r ≤ ‖x-y‖ / Real.exp (-r) := by
    dsimp [B] at hB ⊢
    simpa only [Real.log_exp, sub_neg_eq_add, abs_zero, sub_self, add_zero,
      norm_sub_rev] using hB
  have hsum : r + r + A + B ≤ 2 * (‖x-y‖ / Real.exp (-r)) := by nlinarith
  have hexp : (Real.exp (-r))⁻¹ = Real.exp r := by
    rw [Real.exp_neg, inv_inv]
  calc
    r + r + A + B ≤ 2 * (‖x-y‖ / Real.exp (-r)) := hsum
    _ = 2 * Real.exp r * ‖x-y‖ := by rw [div_eq_mul_inv, hexp]; ring

end

section
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (Y : (ℂ × ℝ) → Ω → ℝ)
  (hmeas : ∀ p, Measurable (Y p)) (hmem : ∀ p, MemLp (Y p) 2 P)
  (hproc : IsGaussianProcess (fun p ω => Y p ω) P) (hmean : ∀ p, (∫ ω, Y p ω ∂P) = 0)
  (hcov : ∀ p q, covariance (Y p) (Y q) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
  (r : ℝ)
include Ω hmeas hmem hproc hmean hcov

/-- The circle L² field on the plane satisfies Kolmogorov's continuity moment criterion. -/
theorem circleL2_isKolmogorovProcess_at_radius :
    ∃ M : ℝ≥0, IsKolmogorovProcess (fun x : ℂ => fun ω => Y (x, r) ω) P 8 4 M := by
  simpa [Function.comp_def] using gaussian_isKolmogorovProcess_of_variance_le
    (hproc.comp_right (fun x => (x, r))) (fun x => hmeas (x, r)) (fun x => hmean (x, r))
    (C := 2 * Real.exp r) (by positivity) (k := 1) (by decide) (fun x y => by
      simpa [dist_eq_norm] using circleL2_increment_variance_le_center Y hmem hcov x y r)

/-- A continuous sample modification at one fixed logarithmic radius. -/
theorem exists_continuous_circleL2_modification_at_radius :
    ∃ Z : ℂ → Ω → ℝ,
      (∀ x, Measurable (Z x)) ∧
      (∀ ω, Continuous (fun x => Z x ω)) ∧
      ∀ x, Z x =ᵐ[P] fun ω => Y (x, r) ω := by
  obtain ⟨M, hM⟩ := circleL2_isKolmogorovProcess_at_radius
    Y hmeas hmem hproc hmean hcov r
  have hcover := isCoverWithBoundedCoveringNumber_balls ℂ
  rw [show Module.finrank ℝ ℂ = 2 by exact Complex.finrank_real_complex] at hcover
  obtain ⟨Z, hZmeas, hZeq, hZholder⟩ := exists_modification_holder' hcover
    hM.IsAEKolmogorovProcess (fun n => by finiteness) (by norm_num) (by norm_num)
  refine ⟨Z, hZmeas, fun ω => continuous_of_locally_holder (r := 1/16) (by norm_num) ?_, hZeq⟩
  intro x
  obtain ⟨U, hU, hh⟩ := hZholder ω x
  exact ⟨U, hU, hh _ (by norm_num) (by norm_num)⟩

end

section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} (X : Ω → Distr) (hX : IsEquatorGFF P X)
include mΩ hX

/-- A canonical circle witness with raw-joint measurability at each fixed radius. -/
theorem exists_raw_equatorGFF_circle_average_witness :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
      ∀ r, Measurable[(equatorGFFRawDistributionSigma X).prod (borel ℂ)]
        (fun p : Ω × ℂ => Xc p.1 p.2 r) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨f, W, Y, hgap, hcross, hW, hY, hproc, hmean, hcov⟩ :=
    exists_equatorGFF_circle_L2_geometry X hX
  have hmeas (p : ℂ × ℝ) : Measurable (Y p) := (hY p).2.1
  have hmem (p : ℂ × ℝ) : MemLp (Y p) 2 P := (hY p).2.2.1
  have hmod (r : ℝ) := exists_continuous_circleL2_modification_at_radius
    Y hmeas hmem hproc hmean hcov r
  choose Z hZmeas hZcont hZeq using hmod
  have hjoint (r : ℝ) := exists_raw_joint_continuous_modification P
    (equatorGFFRawDistributionSigma X)
    (fun ω x => Z r x ω) (ae_of_all P (hZcont r))
    (fun x => ⟨Y (x, r), (hY (x, r)).1, (hZeq r x).symm⟩)
  choose G hGjoint hGae using hjoint
  let Xc : Ω → ℂ → ℝ → ℝ := fun ω x r => G r ω x
  have hmap  :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := by
    dsimp [equatorGFFRawDistributionSigma]
    exact hmap.comap_le
  have hprod : (equatorGFFRawDistributionSigma X).prod (borel ℂ) ≤ mΩ.prod (borel ℂ) := by
    rw [MeasurableSpace.prod, MeasurableSpace.prod]
    exact sup_le_sup (MeasurableSpace.comap_mono hm0) le_rfl
  have hmeasXc (r : ℝ) : Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r) :=
    (hGjoint r).mono hprod le_rfl
  have hXcY (x : ℂ) (r : ℝ) : (fun ω => Xc ω x r) =ᵐ[P] fun ω => Y (x, r) ω := by
    filter_upwards [hGae r, hZeq r x] with ω hG hZ
    exact (hG x).trans hZ
  refine ⟨Xc, ?_, hGjoint⟩
  refine ⟨hmeasXc, fun x r => ?_, ?_⟩
  · exact MemLp.ae_eq (hXcY x r).symm (hmem (x, r))
  · intro x r g hg
    let p : ℂ × ℝ := (x, r)
    let U : ℕ → Lp ℝ 2 P := fun n =>
      (equatorGFF_test_memLp X hX (g n)).toLp (fun ω => X ω (g n))
    have hUT : Tendsto U atTop (𝓝 (W p)) := equatorGFF_testL2_tendsto_to_circle_limit X hX x r
        (f p) (hgap p) (W p) (hW p) g hg
    have hTarget := (hXcY x r).trans (hY p).2.2.2.1
    exact tendsto_eLpNorm_sub_of_L2_versions P U (W p)
      (fun n ω => X ω (g n)) (fun ω => Xc ω x r)
      (fun n => (equatorGFF_test_memLp X hX (g n)).coeFn_toLp.symm)
      hTarget hUT

/-- The supplied equator field has a jointly measurable circle-average process on its raw space. -/
theorem exists_equatorGFF_circle_average_witness :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc := by
  obtain ⟨Xc, hXc, _⟩ := exists_raw_equatorGFF_circle_average_witness X hX
  exact ⟨Xc, hXc⟩

end

end DOZZ.Proofs
