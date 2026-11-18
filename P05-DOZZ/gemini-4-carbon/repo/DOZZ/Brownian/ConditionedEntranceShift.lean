/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedEntranceProbability
public import DOZZ.Brownian.ConditionedKernelCDFOrder
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Drift shift bound for the conditioned entrance quantiles

The entrance density is a Gaussian factor times `y * sinh (ν*y) / ν`, with the Maxwell limit
`y^2` at zero drift. Comparing the shifted densities gives the upper common-quantile bound used
by the rational-drift coupling.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private def shape (ν y : ℝ) : ℝ :=
  if ν = 0 then y ^ 2 else y * Real.sinh (ν * y) / ν

private def score (ν y : ℝ) : ℝ :=
  if ν = 0 then 2 / y else 1 / y + conditionedKernelScore ν y

private lemma shape_pos {ν y : ℝ} (hν : 0 ≤ ν) (hy : 0 < y) : 0 < shape ν y := by
  by_cases hν0 : ν = 0
  · simp [shape, hν0, sq_pos_of_pos hy]
  · have hνp := lt_of_le_of_ne hν (Ne.symm hν0)
    simp only [shape, hν0, ite_false]
    exact div_pos (mul_pos hy (Real.sinh_pos_iff.mpr (mul_pos hνp hy))) hνp

private lemma hasDerivAt_shape {ν y : ℝ} (hν : 0 ≤ ν) (hy : 0 < y) :
    HasDerivAt (shape ν) (shape ν y * score ν y) y := by
  by_cases hν0 : ν = 0
  · subst hν0
    have hs : shape 0 = fun z : ℝ => z ^ 2 := funext fun z => by simp [shape]
    rw [hs]; simp only [score, ite_true]
    convert (hasDerivAt_id y).pow 2 using 1
    · rfl
    · simp only [id_eq]; field_simp [hy.ne']; ring
  · have hνp := lt_of_le_of_ne hν (Ne.symm hν0)
    have hs : shape ν = fun z : ℝ => z * Real.sinh (ν * z) / ν := funext fun z => by simp [shape, hν0]
    have hsc : score ν y = 1 / y + conditionedKernelScore ν y := by simp [score, hν0]
    rw [hs, hsc]
    have harg : HasDerivAt (fun z : ℝ => ν * z) ν y := by
      simpa using (hasDerivAt_id y).const_mul ν
    have hquot : HasDerivAt (fun z : ℝ => z * Real.sinh (ν * z) / ν)
        ((Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν) y := by
      convert (((hasDerivAt_id y).mul ((Real.hasDerivAt_sinh (ν * y)).comp y harg)).div_const ν) using 1
      · rfl
      · simp
    refine hquot.congr_deriv ?_
    dsimp [conditionedKernelScore]
    field_simp [hνp.ne', hy.ne', (Real.sinh_pos_iff.mpr (mul_pos hνp hy)).ne']

private lemma dens_eq_shape {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity ν t y =
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * shape ν y *
        Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) := by
  by_cases hν0 : ν = 0
  · subst hν0
    simp only [conditionedPositiveEntranceDensity, shape, le_rfl, ht, hy, and_self, ite_true]
    rw [Real.rpow_neg ht.le]
    field_simp [(Real.rpow_pos_of_pos ht (3 / 2 : ℝ)).ne']; ring
  · simp [conditionedPositiveEntranceDensity, shape, hν, ht, hy, hν0]

private lemma dens_nonneg {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases hy : 0 < y
  · exact (by rw [dens_eq_shape hν ht hy]; have := shape_pos hν hy; positivity :
      0 < conditionedPositiveEntranceDensity ν t y).le
  · simp [conditionedPositiveEntranceDensity, hν, ht, hy]

/-- The upper common-uniform drift bound for the conditioned entrance law. -/
theorem conditionedPositiveEntranceQuantile_drift_add
    {a b t u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure b t)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure a t)) u + (b - a) * t := by
  have hb : 0 ≤ b := ha.trans hab
  let d := (b - a) * t
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr hab) ht.le
  have hdt : d / t = b - a := mul_div_cancel_right₀ (b - a) ht.ne'
  let ratio : ℝ → ℝ := fun y =>
    Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * (shape b (y + d) / shape a y)
  have hanti : AntitoneOn ratio (Ioi 0) := by
    have hcont : ContinuousOn ratio (Ioi 0) := by
      have hcB : Continuous fun y : ℝ => shape b (y + d) := by
        unfold shape; split_ifs <;> fun_prop
      have hcA : Continuous (shape a) := by unfold shape; split_ifs <;> fun_prop
      exact (by fun_prop : Continuous fun y : ℝ => Real.exp (-(d / t) * y - d ^ 2 / (2 * t))).continuousOn.mul
        (hcB.continuousOn.div hcA.continuousOn fun y hy => (shape_pos ha hy).ne')
    have hder {y : ℝ} (hy : 0 < y) :
        HasDerivAt ratio (ratio y * (-(d / t) + score b (y + d) - score a y)) y := by
      have hlin : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t)) (-(d / t)) y := by
        convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
      have hshB : HasDerivAt (fun z : ℝ => shape b (z + d))
          (shape b (y + d) * score b (y + d)) y := by
        have harg : HasDerivAt (fun z : ℝ => z + d) 1 y := by simpa using (hasDerivAt_id y).add_const d
        convert (hasDerivAt_shape hb (by linarith : 0 < y + d)).comp y harg using 1
        · rfl
        · ring
      have hshA := shape_pos ha hy
      convert ((Real.hasDerivAt_exp _).comp y hlin).mul
        (hshB.div (hasDerivAt_shape ha hy) hshA.ne') using 1
      · rfl
      · dsimp [ratio]; field_simp [hshA.ne']; ring
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
      (fun y hy => (hder (by simpa using hy)).differentiableAt.differentiableWithinAt) fun y hy' => ?_
    have hy : 0 < y := by simpa using hy'
    rw [(hder hy).deriv]
    refine mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le (div_pos (shape_pos hb (by linarith [hy])) (shape_pos ha hy)).le) ?_
    have hantiB : score b (y + d) ≤ score b y := by
      by_cases hb0 : b = 0
      · simp only [score, hb0, ite_true]
        exact div_le_div_of_nonneg_left zero_le_two hy (by linarith)
      · have hbp := lt_of_le_of_ne hb (Ne.symm hb0)
        simp only [score, hb0, ite_false]
        exact add_le_add (one_div_le_one_div_of_le hy (by linarith))
          ((conditionedKernelScore_strictAntiOn_state hbp).antitoneOn hy (by dsimp [Ioi]; linarith) (by linarith))
    have hpar : score b y - score a y ≤ b - a := by
      by_cases ha0 : a = 0
      · subst ha0
        by_cases hb0 : b = 0
        · simp [hb0]
        · have hbp := lt_of_le_of_ne hb (Ne.symm hb0)
          simp only [score, hb0, ite_false, ite_true]
          rw [show 1 / y + conditionedKernelScore b y - 2 / y = conditionedKernelScore b y - 1 / y by ring]
          linarith [(conditionedKernelScore_zero_increment_bounds hbp hy).2]
      · have hap := lt_of_le_of_ne ha (Ne.symm ha0)
        have hbp : 0 < b := hap.trans_le hab
        simp only [score, ha0, hbp.ne', ite_false]
        linarith [(conditionedKernelScore_increment_bounds hap hy hab).2]
    linarith
  -- Shifted density integral comparison and CDF shift
  let g : ℝ → ℝ := fun y => conditionedPositiveEntranceDensity b t (y + d)
  have hemb : MeasurableEmbedding fun y : ℝ => y + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self d
  have hgi : Integrable g volume := by
    have hbase : Integrable (conditionedPositiveEntranceDensity b t)
        ((volume : Measure ℝ).map (fun y => y + d)) := by
      rw [hmap]; exact integrable_conditionedPositiveEntranceDensity hb ht
    exact ((Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding).integrable_map_iff.mp hbase
  have hgu : ∫ y, g y = 1 :=
    (hemb.integral_map (conditionedPositiveEntranceDensity b t)).symm.trans
      (by rw [hmap]; exact conditionedPositiveEntranceDensity_integral_eq_one hb ht)
  let r : ℝ → ℝ := fun y => Real.exp ((a ^ 2 - b ^ 2) * t / 2) * ratio y
  have hcdf (z : ℝ) : ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure a t) z ≤
      ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure b t) (z + d) := by
    rw [conditionedPositiveEntranceMeasure_cdf_eq_integral ha ht,
      conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht]
    have hsh : (∫ y in Iic z, g y) = ∫ y in Iic (z + d), conditionedPositiveEntranceDensity b t y := by
      have h := hemb.setIntegral_map (μ := volume) (conditionedPositiveEntranceDensity b t) (Iic (z + d))
      rw [hmap, show (fun x : ℝ => x + d) ⁻¹' Iic (z + d) = Iic z by ext; simp] at h
      exact h.symm
    rw [← hsh]
    refine integral_Iic_ge_of_shiftedAntitoneDensityRatio (r := r)
      (integrable_conditionedPositiveEntranceDensity ha ht) hgi
      (fun _ => dens_nonneg hb ht)
      (fun y hy => by simp [conditionedPositiveEntranceDensity, ha, ht, hy])
      (conditionedPositiveEntranceDensity_integral_eq_one ha ht) hgu ?_ ?_ rfl
      (fun y hy => ?_) (fun y hy => ?_)
      (fun y hy w hw hyw => mul_le_mul_of_nonneg_left (hanti hy hw hyw) (Real.exp_pos _).le) z
    · refine (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun _ => dens_nonneg hb ht)
        hgi.integrableOn).2 (lt_of_lt_of_le (isOpen_Ioi.measure_pos volume ⟨1, one_pos⟩)
        (measure_mono fun y (hy : 0 < y) => ⟨show g y ≠ 0 from ?_, hy⟩))
      dsimp only [g]
      rw [dens_eq_shape hb ht (by linarith)]
      have := shape_pos hb (by linarith : 0 < y + d)
      positivity
    · have hsp := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hgi
      rw [compl_Ioi, hgu] at hsp
      linarith [setIntegral_nonneg (μ := volume) measurableSet_Iic
        fun y (_ : y ≤ 0) => dens_nonneg (ν := b) (y := y + d) hb ht]
    · dsimp only [g, r, ratio]
      rw [dens_eq_shape hb ht (by linarith), dens_eq_shape ha ht hy]
      have hshA := (shape_pos ha hy).ne'
      have hexp : Real.exp ((a ^ 2 - b ^ 2) * t / 2) * Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          Real.exp (-(y ^ 2) / (2 * t) - a ^ 2 * t / 2) =
          Real.exp (-((y + d) ^ 2) / (2 * t) - b ^ 2 * t / 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; dsimp [d]; field_simp [ht.ne']; ring
      rw [← hexp]; field_simp [hshA]
    · dsimp only [r, ratio]
      exact mul_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _)
        (div_pos (shape_pos hb (by linarith)) (shape_pos ha hy)))
  -- Direct `sInf` comparison without auxiliary shifted measure
  have hSa : {z | u ≤ ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure a t) z}.Nonempty := by
    let := isProbabilityMeasure_conditionedPositiveEntranceMeasure a t ha ht
    obtain ⟨m, hm⟩ := eventually_atTop.1
      ((ProbabilityTheory.tendsto_cdf_atTop _).eventually (Ioi_mem_nhds hu1))
    exact ⟨m, (hm m le_rfl).le⟩
  have hSb : BddBelow {w | u ≤ ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure b t) w} := by
    refine ⟨0, fun w (hw : u ≤ _) => not_lt.mp fun hw0 => ?_⟩
    rw [conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht,
      setIntegral_congr_fun (g := 0) measurableSet_Iic fun y hy => by
        simp [conditionedPositiveEntranceDensity, hb, ht, (mem_Iic.mp hy).trans hw0.le]] at hw
    simp at hw; linarith
  exact sub_le_iff_le_add.mp (le_csInf hSa fun z hz =>
    sub_le_iff_le_add.mpr (csInf_le hSb (hz.trans (hcdf z))))

end DOZZ.Proofs

end
