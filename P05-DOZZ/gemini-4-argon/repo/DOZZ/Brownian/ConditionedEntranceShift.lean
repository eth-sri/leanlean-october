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

open MeasureTheory Filter ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The non-Gaussian factor in the entrance density, including its zero-drift limit. -/
noncomputable def conditionedEntranceShape (ν y : ℝ) : ℝ :=
  if ν = 0 then y ^ 2 else y * Real.sinh (ν * y) / ν

/-- The logarithmic derivative of the entrance shape in its positive state variable. -/
noncomputable def conditionedEntranceScore (ν y : ℝ) : ℝ :=
  if ν = 0 then 2 / y else 1 / y + conditionedKernelScore ν y

private theorem conditionedEntranceShape_pos
    {ν y} (hν : 0 ≤ ν) (hy : 0 < y) :
    0 < conditionedEntranceShape ν y := by
  by_cases hν0 : ν = 0
  · simp [conditionedEntranceShape, hν0, sq_pos_of_pos hy]
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
    simp only [conditionedEntranceShape, hν0, ite_false]
    exact div_pos (mul_pos hy (Real.sinh_pos_iff.mpr (mul_pos hνpos hy))) hνpos

private theorem hasDerivAt_conditionedEntranceShape
    {ν y} (hν : 0 ≤ ν) (hy : 0 < y) :
    HasDerivAt (conditionedEntranceShape ν)
      (conditionedEntranceShape ν y * conditionedEntranceScore ν y) y := by
  by_cases hν0 : ν = 0
  · subst ν
    rw [(show conditionedEntranceShape (0 : ℝ) = fun z : ℝ => z ^ 2 by funext z; simp [conditionedEntranceShape]), (show conditionedEntranceScore (0 : ℝ) y = 2 / y by simp [conditionedEntranceScore])]
    change HasDerivAt (fun z : ℝ => z ^ 2) (y ^ 2 * (2 / y)) y
    convert ((hasDerivAt_id y).pow 2) using 1
    · ext z
      rfl
    · simp only [id_eq]
      field_simp [hy.ne']
      ring_nf
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
    rw [(show conditionedEntranceShape ν = (fun z => z * Real.sinh (ν * z) / ν) by funext z; simp [conditionedEntranceShape, hν0]), (show conditionedEntranceScore ν y = 1 / y + conditionedKernelScore ν y by simp [conditionedEntranceScore, hν0])]
    have hquot' : HasDerivAt (fun z => z * Real.sinh (ν * z) / ν)
        ((Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν) y := by
      convert (((hasDerivAt_id y).mul ((Real.hasDerivAt_sinh (ν * y)).comp y (by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul ν))).div_const ν) using 1
      · ext z
        change z * Real.sinh (ν * z) / ν = (z * Real.sinh (ν * z)) / ν
        rfl
      · change (Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν =
          (1 * Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν
        rw [one_mul]
    exact hquot'.congr_deriv (by dsimp [conditionedKernelScore]; field_simp [hνpos.ne', hy.ne', (Real.sinh_pos_iff.mpr (mul_pos hνpos hy)).ne'])




/-- The shifted entrance-density likelihood ratio. -/
noncomputable def conditionedEntranceShiftedDensityRatio
    (a b t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)

private theorem conditionedEntranceShiftedDensityRatio_hasDerivAt
    {a b t d y} (ha : 0 ≤ a) (hb : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hy : 0 < y) :
    HasDerivAt (conditionedEntranceShiftedDensityRatio a b t d)
      (conditionedEntranceShiftedDensityRatio a b t d y *
        (-(d / t) + conditionedEntranceScore b (y + d) -
          conditionedEntranceScore a y)) y := by
  have hshift : HasDerivAt (fun z => conditionedEntranceShape b (z + d))
      (conditionedEntranceShape b (y + d) * conditionedEntranceScore b (y + d)) y := by
    convert (hasDerivAt_conditionedEntranceShape (le_trans ha hb) (show 0 < y + d by linarith)).comp y (show HasDerivAt (fun z => z + d) 1 y by simpa using (hasDerivAt_id y).add_const d) using 1
    · ext z
      rfl
    · ring
  have hshapeApos := conditionedEntranceShape_pos ha hy
  convert (((Real.hasDerivAt_exp _).comp y (by convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp)).mul (hshift.div (hasDerivAt_conditionedEntranceShape ha hy) hshapeApos.ne')) using 1
  · ext z
    simp [conditionedEntranceShiftedDensityRatio]
  · dsimp [conditionedEntranceShiftedDensityRatio]
    field_simp [hshapeApos.ne']
    ring_nf


private theorem conditionedPositiveEntranceDensity_eq_shape
    {ν t y} (hν : 0 ≤ ν) (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity ν t y =
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
        conditionedEntranceShape ν y *
          Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) := by
  by_cases hν0 : ν = 0
  · subst ν
    rw [conditionedPositiveEntranceDensity]
    simp only [le_rfl, ht, hy, and_self, ite_true]
    rw [Real.rpow_neg (le_of_lt ht)]
    rw [(show conditionedEntranceShape (0 : ℝ) y = y ^ 2 by simp [conditionedEntranceShape])]
    field_simp [(ne_of_gt (Real.rpow_pos_of_pos ht (3 / 2 : ℝ)))]
    ring_nf
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
    rw [conditionedPositiveEntranceDensity, (show conditionedEntranceShape ν y = y * Real.sinh (ν * y) / ν by simp [conditionedEntranceShape, hν0])]
    simp [hν, ht, hy, hν0]


private theorem conditionedPositiveEntranceDensity_nonneg
    {ν t y} (hν : 0 ≤ ν) (ht : 0 < t) :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases hy : 0 < y
  · by_cases hν0 : ν = 0
    · subst ν
      rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
      have : 0 < brownianHeatDensity t y := by
        rw [brownianHeatDensity]
        simp only [ite_eq_left ht]
        positivity
      positivity
    · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
      rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition hνpos ht hy]
      exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht
        (mul_pos hνpos ht) y
  · have hy' : y ≤ 0 := le_of_not_gt hy
    simp [conditionedPositiveEntranceDensity, hν, ht, hy]

private theorem conditionedPositiveEntranceDensity_zero_of_nonpos
    {ν t y} (hν : 0 ≤ ν) (ht : 0 < t) (hy : y ≤ 0) :
    conditionedPositiveEntranceDensity ν t y = 0 := by
  simp [conditionedPositiveEntranceDensity, hν, ht, hy]

private theorem conditionedPositiveEntranceDensity_pos
    {ν t y} (hν : 0 ≤ ν) (ht : 0 < t) (hy : 0 < y) :
    0 < conditionedPositiveEntranceDensity ν t y := by
  rw [conditionedPositiveEntranceDensity_eq_shape hν ht hy]
  exact mul_pos (mul_pos (mul_pos (Real.sqrt_pos.2 (by positivity)) (Real.rpow_pos_of_pos ht _))
    (conditionedEntranceShape_pos hν hy)) (Real.exp_pos _)

private theorem volume_map_add_right d :
    (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
  Measure.IsAddRightInvariant.map_add_right_eq_self d

/-- The entrance law with its endpoint shifted left by `d`. -/
noncomputable def conditionedPositiveEntranceShiftedMeasure (ν t d : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveEntranceDensity ν t (y + d)))

private theorem integrable_conditionedPositiveEntranceDensity_shifted
    {ν t d} (hν : 0 ≤ ν) (ht : 0 < t) :
    Integrable (fun y : ℝ => conditionedPositiveEntranceDensity ν t (y + d))
      (volume : Measure ℝ) := by
  exact ((Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding).integrable_map_iff.mp (show Integrable (conditionedPositiveEntranceDensity ν t) ((volume : Measure ℝ).map (fun y => y + d)) by rw [(volume_map_add_right d)]; exact integrable_conditionedPositiveEntranceDensity hν ht)

private theorem conditionedPositiveEntranceDensity_shifted_integral_eq_one
    {ν t d} (hν : 0 ≤ ν) (ht : 0 < t) :
    ∫ y : ℝ, conditionedPositiveEntranceDensity ν t (y + d) = 1 := by
  calc
    ∫ y, conditionedPositiveEntranceDensity ν t (y + d) =
        ∫ y, conditionedPositiveEntranceDensity ν t y ∂((volume : Measure ℝ).map
          ((Homeomorph.addRight d).toMeasurableEquiv)) := by
            symm
            exact ((Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding).integral_map (conditionedPositiveEntranceDensity ν t)
    _ = ∫ y, conditionedPositiveEntranceDensity ν t y := by
          rw [show (volume : Measure ℝ).map
            ((Homeomorph.addRight d).toMeasurableEquiv) = volume by exact (volume_map_add_right d)]
    _ = 1 := conditionedPositiveEntranceDensity_integral_eq_one hν ht

private theorem isProbabilityMeasure_conditionedPositiveEntranceShiftedMeasure
    ν t d (hν : 0 ≤ ν) (ht : 0 < t) :
    IsProbabilityMeasure (conditionedPositiveEntranceShiftedMeasure ν t d) := by
  rw [isProbabilityMeasure_iff]
  rw [conditionedPositiveEntranceShiftedMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← (ofReal_integral_eq_lintegral_ofReal (integrable_conditionedPositiveEntranceDensity_shifted (d := d) hν ht) (ae_of_all _ (fun y => conditionedPositiveEntranceDensity_nonneg (y := y + d) hν ht))),
    conditionedPositiveEntranceDensity_shifted_integral_eq_one hν ht]
  norm_num

private theorem conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral
    {ν t d z} (hν : 0 ≤ ν) (ht : 0 < t) :
    ProbabilityTheory.cdf (conditionedPositiveEntranceShiftedMeasure ν t d) z =
      ∫ y in Set.Iic z, conditionedPositiveEntranceDensity ν t (y + d) := by
  rw [@ProbabilityTheory.cdf_eq_real
    (conditionedPositiveEntranceShiftedMeasure ν t d) (isProbabilityMeasure_conditionedPositiveEntranceShiftedMeasure ν t d hν ht) z]
  rw [measureReal_def, conditionedPositiveEntranceShiftedMeasure,
    withDensity_apply _ measurableSet_Iic]
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun y => conditionedPositiveEntranceDensity_nonneg (y := y + d) hν ht)) ((integrable_conditionedPositiveEntranceDensity_shifted (d := d) hν ht).integrableOn.aestronglyMeasurable)]

private theorem integral_Iic_add_shift {f : ℝ → ℝ} d z :
    (∫ y in Set.Iic z, f (y + d) ∂(volume : Measure ℝ)) =
      ∫ y in Set.Iic (z + d), f y ∂(volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun x => x + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have h := he.setIntegral_map (μ := (volume : Measure ℝ)) f (Set.Iic (z + d))
  rw [volume_map_add_right d] at h
  rw [(show (fun x => x + d) ⁻¹' Set.Iic (z + d) = Set.Iic z by ext x; simp [Set.mem_Iic])] at h
  exact h.symm

private theorem entranceShift_cdf_superlevel_nonempty
    {μ : Measure ℝ} (hμ : IsProbabilityMeasure μ) {u} (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  let := hμ
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu))
  refine ⟨max a 0, ?_⟩
  change u ≤ ProbabilityTheory.cdf μ (max a 0)
  exact le_of_lt (ha (max a 0) (le_max_left _ _))



/-- The upper common-uniform drift bound for the conditioned entrance law. -/
theorem conditionedPositiveEntranceQuantile_drift_add
    {a b t u} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure b t)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure a t)) u + (b - a) * t := by
  have conditionedPositiveEntranceDensity_shifted_cdf_ge {d} {z} (hd : 0 ≤ d) (hshift : d / t = b - a) : (∫ y in Set.Iic z, conditionedPositiveEntranceDensity a t y) ≤ ∫ y in Set.Iic z, conditionedPositiveEntranceDensity b t (y + d) := by
    have conditionedPositiveEntranceDensity_shifted_factor {y} (hy : 0 < y) : conditionedPositiveEntranceDensity b t (y + d) = Real.exp ((a ^ 2 - b ^ 2) * t / 2) * conditionedEntranceShiftedDensityRatio a b t d y * conditionedPositiveEntranceDensity a t y := by
      rw [conditionedPositiveEntranceDensity_eq_shape (ha.trans hab) ht (show 0 < y + d by linarith),
        conditionedPositiveEntranceDensity_eq_shape ha ht hy]
      dsimp [conditionedEntranceShiftedDensityRatio]
      have hdrel : d = (b - a) * t := by
        have := (div_eq_iff ht.ne').mp hshift
        nlinarith
      let A := (a ^ 2 - b ^ 2) * t / 2
      let B := -(d / t) * y - d ^ 2 / (2 * t)
      let C := -y ^ 2 / (2 * t) - a ^ 2 * t / 2
      have hExpFactor : Real.exp A * Real.exp B * Real.exp C =
          Real.exp (-((y + d) ^ 2) / (2 * t) - b ^ 2 * t / 2) := by
        calc
          Real.exp A * Real.exp B * Real.exp C = Real.exp (A + B) * Real.exp C := by
            rw [← Real.exp_add]
          _ = Real.exp (A + B + C) := by rw [← Real.exp_add]
          _ = Real.exp (-((y + d) ^ 2) / (2 * t) - b ^ 2 * t / 2) := by
            congr 1
            dsimp [A, B, C]
            rw [hdrel]
            field_simp [ht.ne']
            ring_nf
      calc
        _ = Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
              conditionedEntranceShape b (y + d) * (Real.exp A * Real.exp B * Real.exp C) := by
                rw [← hExpFactor]
        _ = _ := by
          dsimp [A, B, C, conditionedEntranceShiftedDensityRatio]
          field_simp [((conditionedEntranceShape_pos ha hy).ne')]
    have conditionedEntranceShiftedDensityRatio_antitoneOn : AntitoneOn (conditionedEntranceShiftedDensityRatio a b t d) (Set.Ioi 0) := by
      have conditionedEntranceScore_mixed_increment_upper {y} {z} (hy : 0 < y) (hyz : y ≤ z) : conditionedEntranceScore b z - conditionedEntranceScore a y ≤ b - a := by
        have conditionedEntranceScore_parameter_increment_upper : conditionedEntranceScore b y - conditionedEntranceScore a y ≤ b - a := by
          have hb := ha.trans hab
          by_cases ha0 : a = 0
          · subst a
            by_cases hb0 : b = 0
            · subst b
              simp [conditionedEntranceScore]
            · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
              simp only [conditionedEntranceScore, hb0, ite_false, ite_eq_left]
              calc
                1 / y + conditionedKernelScore b y - 2 / y =
                    conditionedKernelScore b y - 1 / y := by ring
                _ ≤ b - 0 := by simpa using (conditionedKernelScore_zero_increment_bounds hbpos hy).2
          · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            by_cases hb0 : b = 0
            · have : a = 0 := le_antisymm (by simpa [hb0] using hab) ha
              contradiction
            · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
              simp only [conditionedEntranceScore, ha0, hb0, ite_false]
              have := conditionedKernelScore_increment_bounds hapos hy hab
              linarith
        have conditionedEntranceScore_antitoneOn_state {ν} (hν : 0 ≤ ν) : AntitoneOn (conditionedEntranceScore ν) (Set.Ioi 0) := by
          intro y hy z hz hyz
          by_cases hν0 : ν = 0
          · have hscore : conditionedEntranceScore ν = fun x : ℝ => 2 / x := by
              funext x
              simp [conditionedEntranceScore, hν0]
            rw [hscore]
            calc
              2 / z = 2 * (1 / z) := by ring
              _ ≤ 2 * (1 / y) := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by simpa using hy) (by simpa using hyz)) (by norm_num)
              _ = 2 / y := by ring
          · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
            simp only [conditionedEntranceScore, hν0, ite_false]
            apply add_le_add
            · exact one_div_le_one_div_of_le (by simpa using hy) (by simpa using hyz)
            · exact ((conditionedKernelScore_strictAntiOn_state hνpos).antitoneOn
                (by simpa using hy) (by simpa using hz) hyz)
        have hstate : conditionedEntranceScore b z ≤ conditionedEntranceScore b y :=
          conditionedEntranceScore_antitoneOn_state (le_trans ha hab)
            (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr (lt_of_lt_of_le hy hyz)) hyz
        have hparam := conditionedEntranceScore_parameter_increment_upper
        linarith
      apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) (by change ContinuousOn (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * (conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)) (Set.Ioi 0); exact (show Continuous (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) by fun_prop).continuousOn.mul (by apply ((show Continuous (conditionedEntranceShape b) by unfold conditionedEntranceShape; split_ifs <;> fun_prop).comp (continuous_id.add continuous_const)).continuousOn.div (show Continuous (conditionedEntranceShape a) by unfold conditionedEntranceShape; split_ifs <;> fun_prop).continuousOn; intro y hy; exact (ne_of_gt (conditionedEntranceShape_pos ha (by simpa using hy)))))
      · intro y hy
        exact (conditionedEntranceShiftedDensityRatio_hasDerivAt ha hab ht hd
          (by simpa using hy)).differentiableAt.differentiableWithinAt
      · intro y hy
        have hypos : 0 < y := by simpa using hy
        rw [(conditionedEntranceShiftedDensityRatio_hasDerivAt ha hab ht hd hypos).deriv]
        have hbracket : -(d / t) + conditionedEntranceScore b (y + d) -
            conditionedEntranceScore a y ≤ 0 := by
          rw [hshift]
          exact sub_nonpos.mpr (by
            have := conditionedEntranceScore_mixed_increment_upper hypos
              (z := y + d) (by linarith [hd])
            linarith)
        exact mul_nonpos_of_nonneg_of_nonpos (by dsimp [conditionedEntranceShiftedDensityRatio]; exact mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (div_pos (conditionedEntranceShape_pos (le_trans ha hab) (by linarith [hypos, hd])) (conditionedEntranceShape_pos ha hypos)))) hbracket
    have hb := ha.trans hab
    let f : ℝ → ℝ := conditionedPositiveEntranceDensity a t
    let g : ℝ → ℝ := fun y => conditionedPositiveEntranceDensity b t (y + d)
    let C : ℝ := Real.exp ((a ^ 2 - b ^ 2) * t / 2)
    let r : ℝ → ℝ := fun y => C * conditionedEntranceShiftedDensityRatio a b t d y
    have hg := integrable_conditionedPositiveEntranceDensity_shifted (d := d) hb ht
    have hng : ∀ y, 0 ≤ g y := fun y =>
      conditionedPositiveEntranceDensity_nonneg (y := y + d) hb ht
    have hunitg : ∫ y, g y = 1 :=
      conditionedPositiveEntranceDensity_shifted_integral_eq_one hb ht
    have hmassPos : 0 < ∫ y in Set.Ioi 0, g y := by
      have hpos : ∀ y, 0 < y → 0 < g y := by
        intro y hy
        dsimp [g]
        exact conditionedPositiveEntranceDensity_pos hb ht (by linarith)
      have hsubset : Set.Ioi (0 : ℝ) ⊆ Function.support g ∩ Set.Ioi 0 := by
        intro y hy
        refine ⟨?_, hy⟩
        simp only [Function.mem_support, ne_eq]
        exact (ne_of_gt (hpos y hy))
      exact (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun y => hng y)) hg.integrableOn).2 (lt_of_lt_of_le (isOpen_Ioi.measure_pos (volume : Measure ℝ) ⟨1, by norm_num⟩) (measure_mono hsubset))
    have hmassLe : (∫ y in Set.Ioi 0, g y) ≤ 1 := by
      have : 0 ≤ ∫ y in Set.Iic 0, g y :=
        setIntegral_nonneg measurableSet_Iic (fun y _ => hng y)
      have hsplit := integral_add_compl (μ := (volume : Measure ℝ)) (f := g)
        (s := Set.Ioi 0) measurableSet_Ioi hg
      rw [Set.compl_Ioi] at hsplit
      rw [hunitg] at hsplit
      linarith
    exact integral_Iic_ge_of_shiftedAntitoneDensityRatio (integrable_conditionedPositiveEntranceDensity ha ht) hg hng (show ∀ y, y ≤ 0 → f y = 0 by intro y hy; exact conditionedPositiveEntranceDensity_zero_of_nonpos ha ht hy) (conditionedPositiveEntranceDensity_integral_eq_one ha ht) hunitg
      hmassPos hmassLe (by rfl) (show ∀ y, 0 < y → g y = r y * f y by intro y hy; simpa [g, r, C, f] using conditionedPositiveEntranceDensity_shifted_factor hy) (by intro y hy; dsimp [r, C]; exact mul_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _) (div_pos (conditionedEntranceShape_pos hb (by linarith [hy, hd])) (conditionedEntranceShape_pos ha hy)))) (by intro y hy z hz hyz; dsimp [r]; apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _)); exact conditionedEntranceShiftedDensityRatio_antitoneOn hy hz hyz) z
  have entranceShift_cdf_superlevel_bddBelow {μ : Measure ℝ} (hμ : IsProbabilityMeasure μ) {u} (hu : 0 < u) (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) : BddBelow {x | u ≤ ProbabilityTheory.cdf μ x} := by
    let := hμ
    refine ⟨0, ?_⟩
    intro x hx
    change u ≤ ProbabilityTheory.cdf μ x at hx
    by_contra hnot
    rw [hzero x (le_of_lt (lt_of_not_ge hnot))] at hx
    linarith
  have hb := ha.trans hab
  let d := (b - a) * t
  let μsmall := conditionedPositiveEntranceMeasure a t
  let μlarge := conditionedPositiveEntranceMeasure b t
  let μshift := conditionedPositiveEntranceShiftedMeasure b t d
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure a t ha ht
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure b t hb ht
  have : IsProbabilityMeasure μshift :=
    isProbabilityMeasure_conditionedPositiveEntranceShiftedMeasure b t d hb ht
  have hnonempty : {z | u ≤ ProbabilityTheory.cdf μsmall z}.Nonempty :=
    entranceShift_cdf_superlevel_nonempty hμsmall hu1
  have hquantShift : cdfGeneralizedQuantile (ProbabilityTheory.cdf μshift) u =
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μlarge) u - d := by
    let S := {z | u ≤ ProbabilityTheory.cdf μlarge z}
    have hSnonempty : S.Nonempty := entranceShift_cdf_superlevel_nonempty hμlarge hu1
    have hzeroLarge z (hz : z ≤ 0) : ProbabilityTheory.cdf μlarge z = 0 := by
      rw [conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht]
      rw [setIntegral_congr_fun measurableSet_Iic
        (fun y hy => conditionedPositiveEntranceDensity_zero_of_nonpos hb ht
          (hy.trans hz))]
      simp
    have hshiftcdf z : ProbabilityTheory.cdf μshift z =
        ProbabilityTheory.cdf μlarge (z + d) := by
      rw [conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral hb ht,
        conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht,
        integral_Iic_add_shift d z]
    have hset : {z | u ≤ ProbabilityTheory.cdf μshift z} =
        (fun z => z - d) '' S := by
      ext z
      constructor
      · intro hz
        refine ⟨z + d, ?_, ?_⟩
        · change u ≤ ProbabilityTheory.cdf μshift z at hz
          rw [hshiftcdf] at hz
          simpa [S] using hz
        · ring
      · rintro ⟨y, hy, rfl⟩
        change u ≤ ProbabilityTheory.cdf μshift (y - d)
        rw [hshiftcdf]
        simpa [S] using hy
    have himage : (fun z => z - d) '' S = (OrderIso.addRight (-d)) '' S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by rw [OrderIso.addRight_apply]; ring⟩
      · rintro ⟨y, hy, hz⟩
        refine ⟨y, hy, ?_⟩
        rw [OrderIso.addRight_apply] at hz
        exact hz
    unfold cdfGeneralizedQuantile
    rw [hset]
    exact (by rw [himage, ← ((OrderIso.addRight (-d)).map_csInf' hSnonempty (entranceShift_cdf_superlevel_bddBelow hμlarge hu hzeroLarge)), OrderIso.addRight_apply]; ring)
  have hzeroShift z (hz : z ≤ -d) : ProbabilityTheory.cdf μshift z = 0 := by
    rw [conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral hb ht]
    have hzero : ∀ y, y ∈ Set.Iic z →
        conditionedPositiveEntranceDensity b t (y + d) = 0 := by
      intro y hy
      exact conditionedPositiveEntranceDensity_zero_of_nonpos hb ht (by
        change y ≤ z at hy
        linarith [hy, hz])
    rw [setIntegral_congr_fun measurableSet_Iic hzero]
    simp
  have hshiftBdd : BddBelow {z | u ≤ ProbabilityTheory.cdf μshift z} := by
    refine ⟨-d, ?_⟩
    intro z hz
    change u ≤ ProbabilityTheory.cdf μshift z at hz
    by_contra hnot
    rw [hzeroShift z (le_of_lt (lt_of_not_ge hnot))] at hz
    linarith
  have hqorder := cdfGeneralizedQuantile_antitone (by intro z; rw [conditionedPositiveEntranceMeasure_cdf_eq_integral ha ht, conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral hb ht]; exact conditionedPositiveEntranceDensity_shifted_cdf_ge (mul_nonneg (sub_nonneg.mpr hab) ht.le) (by dsimp [d]; field_simp [ht.ne'])) hnonempty hshiftBdd
  rw [hquantShift] at hqorder
  nlinarith [hqorder]

end DOZZ.Proofs

end
