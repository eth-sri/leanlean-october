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
section
variable {ν y : ℝ}
section
variable (hν : 0 ≤ ν) (hy : 0 < y)
include hν hy

private theorem conditionedEntranceShape_pos
    :
    0 < conditionedEntranceShape ν y := by
  by_cases hν0 : ν = 0
  · simp [conditionedEntranceShape, hν0, sq_pos_of_pos hy]
  · have hνpos := lt_of_le_of_ne hν (Ne.symm hν0)
    simp only [conditionedEntranceShape, hν0, ite_false]
    positivity

private theorem hasDerivAt_conditionedEntranceShape
    :
    HasDerivAt (conditionedEntranceShape ν)
      (conditionedEntranceShape ν y * conditionedEntranceScore ν y) y := by
  by_cases hν0 : ν = 0
  · subst ν
    have hshape : conditionedEntranceShape 0 = fun z : ℝ => z ^ 2 := by
      funext z
      simp [conditionedEntranceShape]
    have hscore : conditionedEntranceScore 0 y = 2 / y := by
      simp [conditionedEntranceScore]
    rw [hshape, hscore]
    change HasDerivAt (fun z : ℝ => z ^ 2) _ y
    convert ((hasDerivAt_id y).pow 2) using 1
    · rfl
    grind
  · have hνpos := lt_of_le_of_ne hν (Ne.symm hν0)
    have harg : HasDerivAt (fun z : ℝ => ν * z) ν y := by
      simpa using (hasDerivAt_id y).const_mul ν
    have hquot := ((hasDerivAt_id y).mul ((Real.hasDerivAt_sinh (ν * y)).comp y harg)).div_const ν
    have hsinhpos := Real.sinh_pos_iff.mpr (mul_pos hνpos hy)
    have halg : (Real.sinh (ν * y) + y * (Real.cosh (ν * y) * ν)) / ν =
        (y * Real.sinh (ν * y) / ν) *
          (1 / y + conditionedKernelScore ν y) := by
      dsimp [conditionedKernelScore]
      field_simp
    have hshape : conditionedEntranceShape ν =
        (fun z : ℝ => z * Real.sinh (ν * z) / ν) := by
      funext z
      simp [conditionedEntranceShape, hν0]
    have hscore : conditionedEntranceScore ν y =
        1 / y + conditionedKernelScore ν y := by
      simp [conditionedEntranceScore, hν0]
    simp_all

end

end

private theorem conditionedEntranceScore_antitoneOn_state
    {ν : ℝ} (hν : 0 ≤ ν) : AntitoneOn (conditionedEntranceScore ν) (Set.Ioi 0) := by
  intro y hy z hz hyz
  by_cases hν0 : ν = 0
  · have hscore : conditionedEntranceScore ν = fun x : ℝ => 2 / x := by
      funext x
      simp [conditionedEntranceScore, hν0]
    rw [hscore]
    bound
  · have hνpos := lt_of_le_of_ne hν (Ne.symm hν0)
    simp only [conditionedEntranceScore, hν0, ite_false]
    apply add_le_add
    · bound
    · exact ((conditionedKernelScore_strictAntiOn_state hνpos).antitoneOn
        (by assumption) (by assumption) hyz)

private theorem conditionedEntranceScore_parameter_increment_upper
    {a b y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 < y) :
    conditionedEntranceScore b y - conditionedEntranceScore a y ≤ b - a := by
  have hb := ha.trans hab
  by_cases ha0 : a = 0
  · subst a
    by_cases hb0 : b = 0
    · simp_all
    · have hbpos := lt_of_le_of_ne hb (Ne.symm hb0)
      simp only [conditionedEntranceScore, hb0, ite_false, ite_eq_left]
      calc
        1 / y + conditionedKernelScore b y - 2 / y =
            conditionedKernelScore b y - 1 / y := by ring
        _ ≤ b - 0 := by simpa using (conditionedKernelScore_zero_increment_bounds hbpos hy).2
  · have hapos := lt_of_le_of_ne ha (Ne.symm ha0)
    by_cases hb0 : b = 0
    · linarith
    · have hbpos := lt_of_le_of_ne hb (Ne.symm hb0)
      simp only [conditionedEntranceScore, ha0, hb0, ite_false]
      have hs := conditionedKernelScore_increment_bounds hapos hy hab
      linarith

private theorem conditionedEntranceScore_mixed_increment_upper
    {a b y z : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hy : 0 < y)
    (hyz : y ≤ z) :
    conditionedEntranceScore b z - conditionedEntranceScore a y ≤ b - a := by
  have hstate :=
    conditionedEntranceScore_antitoneOn_state (le_trans ha hab)
      (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr (lt_of_lt_of_le hy hyz)) hyz
  have hparam := conditionedEntranceScore_parameter_increment_upper ha hab hy
  linarith

/-- The shifted entrance-density likelihood ratio. -/
noncomputable def conditionedEntranceShiftedDensityRatio
    (a b t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)

private theorem conditionedEntranceShiftedDensityRatio_hasDerivAt
    {a b t d y : ℝ} (ha : 0 ≤ a) (hb : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hy : 0 < y) :
    HasDerivAt (conditionedEntranceShiftedDensityRatio a b t d)
      (conditionedEntranceShiftedDensityRatio a b t d y *
        (-(d / t) + conditionedEntranceScore b (y + d) -
          conditionedEntranceScore a y)) y := by
  have hyD : 0 < y + d := by linarith
  have hlinear : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hshift : HasDerivAt (fun z : ℝ => conditionedEntranceShape b (z + d))
      (conditionedEntranceShape b (y + d) * conditionedEntranceScore b (y + d)) y := by
    have harg : HasDerivAt (fun z : ℝ => z + d) 1 y := by
      simpa using (hasDerivAt_id y).add_const d
    convert (hasDerivAt_conditionedEntranceShape (le_trans ha hb) hyD).comp y harg using 1
    · rfl
    · ring
  have hshapeApos := conditionedEntranceShape_pos ha hy
  have hquot := hshift.div (hasDerivAt_conditionedEntranceShape ha hy) hshapeApos.ne'
  convert (((Real.hasDerivAt_exp _).comp y hlinear).mul hquot) using 1
  · rfl
  · dsimp [conditionedEntranceShiftedDensityRatio]
    field_simp [hshapeApos.ne']
    ring_nf

/-- The shifted entrance likelihood ratio is antitone for the exact shift
`d = (b-a)t`, including the Maxwell endpoint `a=0`. -/
theorem conditionedEntranceShiftedDensityRatio_antitoneOn
    {a b t d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = b - a) :
    AntitoneOn (conditionedEntranceShiftedDensityRatio a b t d) (Set.Ioi 0) := by
  have hcont : ContinuousOn (conditionedEntranceShiftedDensityRatio a b t d) (Set.Ioi 0) := by
    change ContinuousOn (fun y => Real.exp _ *
      (conditionedEntranceShape b _ / conditionedEntranceShape a y)) (Set.Ioi 0)
    have hshape : Continuous (conditionedEntranceShape b) := by
      unfold conditionedEntranceShape
      split_ifs <;> fun_prop
    have hshapeB : Continuous (fun y => conditionedEntranceShape b (y + d)) :=
      by fun_prop
    have hshapeA : Continuous (conditionedEntranceShape a) := by
      unfold conditionedEntranceShape
      split_ifs <;> fun_prop
    have hratio : ContinuousOn
        (fun y => conditionedEntranceShape b (y + d) / conditionedEntranceShape a y)
        (Set.Ioi 0) := by
      apply hshapeB.continuousOn.div hshapeA.continuousOn
      intro y hy
      exact (ne_of_gt (conditionedEntranceShape_pos ha (by assumption)))
    fun_prop
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    exact (conditionedEntranceShiftedDensityRatio_hasDerivAt ha hab ht hd
      (by simp_all)).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simp_all
    rw [(conditionedEntranceShiftedDensityRatio_hasDerivAt ha hab ht hd hypos).deriv]
    have hbracket : -(d / t) + conditionedEntranceScore b (y + d) -
        conditionedEntranceScore a y ≤ 0 := by
      rw [hshift]
      exact sub_nonpos.mpr (by
        have h := conditionedEntranceScore_mixed_increment_upper ha hab hypos
          (z := y + d) (by linarith)
        linarith)
    have hratio : 0 ≤ conditionedEntranceShiftedDensityRatio a b t d y := by
      dsimp [conditionedEntranceShiftedDensityRatio]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (div_pos
        (conditionedEntranceShape_pos (le_trans ha hab) (by linarith))
        (conditionedEntranceShape_pos ha hypos)))
    nlinarith

private theorem conditionedPositiveEntranceDensity_eq_shape
    {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity ν t y =
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
        conditionedEntranceShape ν y *
          Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) := by
  by_cases hν0 : ν = 0
  · subst ν
    rw [conditionedPositiveEntranceDensity]
    simp only [le_rfl, ht, hy, and_self, ite_true]
    rw [Real.rpow_neg (le_of_lt ht)]
    have hpow :=
      ne_of_gt (Real.rpow_pos_of_pos ht (3 / 2))
    have hshape : conditionedEntranceShape 0 y = y ^ 2 := by
      simp [conditionedEntranceShape]
    grind
  · have hνpos := lt_of_le_of_ne hν (Ne.symm hν0)
    have hshape : conditionedEntranceShape ν y = y * Real.sinh (ν * y) / ν := by
      simp [conditionedEntranceShape, hν0]
    rw [conditionedPositiveEntranceDensity, hshape]
    simp_all

private theorem conditionedPositiveEntranceDensity_shifted_factor
    {a b t d y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = b - a) (hy : 0 < y) :
    conditionedPositiveEntranceDensity b t (y + d) =
      Real.exp ((a ^ 2 - b ^ 2) * t / 2) *
        conditionedEntranceShiftedDensityRatio a b t d y *
          conditionedPositiveEntranceDensity a t y := by
  have hyD : 0 < y + d := by linarith
  rw [conditionedPositiveEntranceDensity_eq_shape (ha.trans hab) ht hyD,
    conditionedPositiveEntranceDensity_eq_shape ha ht hy]
  dsimp [conditionedEntranceShiftedDensityRatio]
  have hshapeA : conditionedEntranceShape a y ≠ 0 :=
    (conditionedEntranceShape_pos ha hy).ne'
  have hdrel : d = (b - a) * t := by
    grind
  let A := (a ^ 2 - b ^ 2) * t / 2
  let B := -(d / t) * y - d ^ 2 / (2 * t)
  let C := -y ^ 2 / (2 * t) - a ^ 2 * t / 2
  have hExpFactor : Real.exp A * Real.exp B * Real.exp C =
      Real.exp (-((y + d) ^ 2) / (2 * t) - b ^ 2 * t / 2) := by
    calc
      Real.exp A * Real.exp B * Real.exp C = Real.exp _ * Real.exp C := by
        rw [← Real.exp_add]
      _ = Real.exp _ := by rw [← Real.exp_add]
      _ = Real.exp _ := by
        congr 1
        dsimp [A, B, C]
        rw [hdrel]
        field_simp [ht.ne']
        ring_nf
  calc
    _ = Real.sqrt _ * t ^ (-(3 / 2 : ℝ)) *
          conditionedEntranceShape b _ * (Real.exp A * Real.exp B * Real.exp C) := by
            rw [← hExpFactor]
    _ = _ := by
      dsimp [A, B, C, conditionedEntranceShiftedDensityRatio]
      field_simp [hshapeA]
section
variable {ν t y : ℝ}
section
variable (hν : 0 ≤ ν) (ht : 0 < t)
include hν ht

private theorem conditionedPositiveEntranceDensity_nonneg
    :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases hy : 0 < y
  · by_cases hν0 : ν = 0
    · subst ν
      rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
      have hheat : 0 < brownianHeatDensity t y := by
        rw [brownianHeatDensity]
        simp only [ite_eq_left ht]
        positivity
      positivity
    · have hνpos := lt_of_le_of_ne hν (Ne.symm hν0)
      rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition hνpos ht hy]
      exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht
        (mul_pos hνpos ht) y
  · have hy' := le_of_not_gt hy
    simp [conditionedPositiveEntranceDensity, hν, ht, hy]

private theorem conditionedPositiveEntranceDensity_pos
    (hy : 0 < y) :
    0 < conditionedPositiveEntranceDensity ν t y := by
  rw [conditionedPositiveEntranceDensity_eq_shape hν ht hy]
  have hsqrt : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hpow : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  exact mul_pos (mul_pos (mul_pos hsqrt hpow)
    (conditionedEntranceShape_pos hν hy)) (Real.exp_pos _)

end

end

private theorem volume_map_add_right (d : ℝ) :
    (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
  Measure.IsAddRightInvariant.map_add_right_eq_self d

/-- The entrance law with its endpoint shifted left by `d`. -/
noncomputable def conditionedPositiveEntranceShiftedMeasure (ν t d : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveEntranceDensity ν t (y + d)))
section
variable {ν t d : ℝ}
section
variable (hν : 0 ≤ ν) (ht : 0 < t)
include hν ht

private theorem integrable_conditionedPositiveEntranceDensity_shifted
    :
    Integrable (fun y : ℝ => conditionedPositiveEntranceDensity ν t (y + d))
      (volume : Measure ℝ) := by
  have he :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hbase : Integrable (conditionedPositiveEntranceDensity ν t)
      (volume.map (fun y => y + d)) := by
    rw [(volume_map_add_right d)]
    exact integrable_conditionedPositiveEntranceDensity hν ht
  exact he.integrable_map_iff.mp hbase

private theorem conditionedPositiveEntranceDensity_shifted_integral_eq_one
    :
    ∫ y : ℝ, conditionedPositiveEntranceDensity ν t (y + d) = 1 := by
  have he :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap := volume_map_add_right d
  calc
    ∫ y, conditionedPositiveEntranceDensity ν t _ =
        ∫ y, conditionedPositiveEntranceDensity ν t y ∂((volume : Measure ℝ).map
          ((Homeomorph.addRight d).toMeasurableEquiv)) := by
            symm
            exact he.integral_map _
    _ = ∫ y, conditionedPositiveEntranceDensity ν t y := by
          simp_all
    _ = 1 := conditionedPositiveEntranceDensity_integral_eq_one hν ht

end

end

private theorem isProbabilityMeasure_conditionedPositiveEntranceShiftedMeasure
    (ν t d : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) :
    IsProbabilityMeasure (conditionedPositiveEntranceShiftedMeasure ν t d) := by
  rw [isProbabilityMeasure_iff]
  have hnonneg : 0 ≤ᵐ[volume]
      (fun y : ℝ => conditionedPositiveEntranceDensity ν t _) :=
    ae_of_all _ (fun y => conditionedPositiveEntranceDensity_nonneg (y := y + d) hν ht)
  have hlin := ofReal_integral_eq_lintegral_ofReal (integrable_conditionedPositiveEntranceDensity_shifted (d := d) hν ht) hnonneg
  rw [conditionedPositiveEntranceShiftedMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← hlin,
    conditionedPositiveEntranceDensity_shifted_integral_eq_one hν ht]
  norm_num

private theorem conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral
    {ν t d z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    ProbabilityTheory.cdf (conditionedPositiveEntranceShiftedMeasure ν t d) z =
      ∫ y in Set.Iic z, conditionedPositiveEntranceDensity ν t (y + d) := by
  rw [@ProbabilityTheory.cdf_eq_real
    (conditionedPositiveEntranceShiftedMeasure ν t d) (isProbabilityMeasure_conditionedPositiveEntranceShiftedMeasure ν t d hν ht) z]
  rw [measureReal_def, conditionedPositiveEntranceShiftedMeasure,
    withDensity_apply _ measurableSet_Iic]
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Iic z)]
      (fun y : ℝ => conditionedPositiveEntranceDensity ν t (y + d)) :=
    ae_of_all _ (fun y => conditionedPositiveEntranceDensity_nonneg (y := y + d) hν ht)
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => conditionedPositiveEntranceDensity ν t _)
      ((volume : Measure ℝ).restrict (Set.Iic z)) := (integrable_conditionedPositiveEntranceDensity_shifted (d := d) hν ht).integrableOn.aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]

private theorem integral_Iic_add_shift {f : ℝ → ℝ} (d z : ℝ) :
    (∫ y in Set.Iic z, f (y + d) ∂(volume : Measure ℝ)) =
      ∫ y in Set.Iic (z + d), f y ∂(volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun x : ℝ => x + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have h := he.setIntegral_map (μ := (volume : Measure ℝ)) f (Set.Iic (z + d))
  rw [volume_map_add_right d] at h
  simp_all
section
variable {μ : Measure ℝ}
section
variable (hμ : IsProbabilityMeasure μ) {u : ℝ}
include hμ

private theorem entranceShift_cdf_superlevel_nonempty
    (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  let := hμ
  have hev :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max a 0, ?_⟩
  grind

private theorem entranceShift_cdf_superlevel_bddBelow
    (hu : 0 < u)
    (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) :
    BddBelow {x | u ≤ ProbabilityTheory.cdf μ x} := by
  let := hμ
  refine ⟨0, ?_⟩
  intro x hx
  grind

end

end

/-- Translating the larger-drift entrance density left by its drift increment gives a CDF that
dominates the smaller-drift entrance CDF. -/
theorem conditionedPositiveEntranceDensity_shifted_cdf_ge
    {a b t d z : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = b - a) :
    (∫ y in Set.Iic z, conditionedPositiveEntranceDensity a t y) ≤
      ∫ y in Set.Iic z, conditionedPositiveEntranceDensity b t (y + d) := by
  have hb : 0 ≤ b := ha.trans hab
  let f := conditionedPositiveEntranceDensity a t
  let g : ℝ → ℝ := fun y => conditionedPositiveEntranceDensity b t (y + d)
  let C := Real.exp ((a ^ 2 - b ^ 2) * t / 2)
  let r : ℝ → ℝ := fun y => C * conditionedEntranceShiftedDensityRatio a b t d y
  have hf : Integrable f (volume : Measure ℝ) := integrable_conditionedPositiveEntranceDensity ha ht
  have hg : Integrable g (volume : Measure ℝ) :=
    integrable_conditionedPositiveEntranceDensity_shifted hb ht
  have hng : ∀ y, 0 ≤ g y := fun y =>
    conditionedPositiveEntranceDensity_nonneg hb ht
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact DOZZ.Proofs.conditionedPositiveEntranceDensity_eq_zero_of_nonpos ha ht hy
  have hunitf : ∫ y, f y = 1 := conditionedPositiveEntranceDensity_integral_eq_one ha ht
  have hunitg : ∫ y, g y = 1 :=
    conditionedPositiveEntranceDensity_shifted_integral_eq_one hb ht
  have hmassPos : 0 < ∫ y in Set.Ioi 0, g y := by
    have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] g :=
      ae_of_all _ hng
    have hpos : ∀ y, 0 < y → 0 < g y := by
      intro y hy
      have hyD : 0 < y + d := by linarith
      exact conditionedPositiveEntranceDensity_pos hb ht hyD
    have hIoi : 0 < volume (Set.Ioi (0 : ℝ)) :=
      by simp
    have hsubset : Set.Ioi (0 : ℝ) ⊆ Function.support g ∩ Set.Ioi 0 := by
      intro y hy
      refine ⟨?_, hy⟩
      exact (ne_of_gt (hpos y hy))
    have hsupport : 0 < volume (Function.support g ∩ Set.Ioi 0) :=
      lt_of_lt_of_le hIoi (measure_mono hsubset)
    exact (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hg.integrableOn).2 hsupport
  have hmassLe : (∫ y in Set.Ioi 0, g y) ≤ 1 := by
    have hcomp : 0 ≤ ∫ y in Set.Iic 0, g y :=
      setIntegral_nonneg measurableSet_Iic (fun y _ => hng y)
    have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
      (s := Set.Ioi 0) measurableSet_Ioi hg
    rw [Set.compl_Ioi] at hsplit
    rw [hunitg] at hsplit
    linarith
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    simpa [g, r, C, f] using
      conditionedPositiveEntranceDensity_shifted_factor ha hab ht hd hshift hy
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    exact mul_pos (Real.exp_pos _) (mul_pos (Real.exp_pos _)
      (div_pos (conditionedEntranceShape_pos hb (by linarith))
        (conditionedEntranceShape_pos ha hy)))
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    intro y hy z hz hyz
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
    exact conditionedEntranceShiftedDensityRatio_antitoneOn ha hab ht hd hshift hy hz hyz
  exact integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero hunitf hunitg
    hmassPos hmassLe (by rfl) hfactor hrpos hratio z

/-- The upper common-uniform drift bound for the conditioned entrance law. -/
theorem conditionedPositiveEntranceQuantile_drift_add
    {a b t u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure b t)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure a t)) u + (b - a) * t := by
  have hb := ha.trans hab
  let d := (b - a) * t
  have hdt : d / t = b - a := by
    grind
  let μsmall := conditionedPositiveEntranceMeasure a t
  let μlarge := conditionedPositiveEntranceMeasure b t
  let μshift := conditionedPositiveEntranceShiftedMeasure b t d
  have hμsmall :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure a t ha ht
  have hμlarge :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure b t hb ht
  have hμshift :=
    isProbabilityMeasure_conditionedPositiveEntranceShiftedMeasure b t d hb ht
  have hzeroSmall (z : ℝ) (hz : z ≤ 0) : ProbabilityTheory.cdf μsmall z = 0 := by
    rw [conditionedPositiveEntranceMeasure_cdf_eq_integral ha ht]
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => DOZZ.Proofs.conditionedPositiveEntranceDensity_eq_zero_of_nonpos ha ht (hy.trans hz))]
    simp
  have hnonempty :=
    entranceShift_cdf_superlevel_nonempty hμsmall hu1
  have hbddSmall :=
    entranceShift_cdf_superlevel_bddBelow hμsmall hu
      (fun z hz => hzeroSmall z hz)
  have hcdfOrder : ∀ z, ProbabilityTheory.cdf μsmall z ≤ ProbabilityTheory.cdf μshift z := by
    intro z
    rw [conditionedPositiveEntranceMeasure_cdf_eq_integral ha ht,
      conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral hb ht]
    exact conditionedPositiveEntranceDensity_shifted_cdf_ge ha hab ht (mul_nonneg (sub_nonneg.mpr hab) ht.le) hdt
  have hquantShift : cdfGeneralizedQuantile (ProbabilityTheory.cdf μshift) u =
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μlarge) u - d := by
    let S := {z | u ≤ ProbabilityTheory.cdf μlarge z}
    have hzeroLarge (z : ℝ) (hz : z ≤ 0) : ProbabilityTheory.cdf μlarge z = 0 := by
      rw [conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht]
      rw [setIntegral_congr_fun measurableSet_Iic
        (fun y hy => DOZZ.Proofs.conditionedPositiveEntranceDensity_eq_zero_of_nonpos hb ht
          (hy.trans hz))]
      simp
    have hshiftcdf (z : ℝ) : ProbabilityTheory.cdf μshift z =
        ProbabilityTheory.cdf μlarge (z + d) := by
      rw [conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral hb ht,
        conditionedPositiveEntranceMeasure_cdf_eq_integral hb ht,
        integral_Iic_add_shift d z]
    have hset : {z | u ≤ ProbabilityTheory.cdf μshift z} =
        (fun z : ℝ => z - d) '' S := by
      ext z
      constructor
      · intro hz
        refine ⟨z + d, ?_, ?_⟩
        · aesop
        · ring
      · rintro ⟨y, hy, rfl⟩
        aesop
    have himage : (fun z : ℝ => z - d) '' S = (OrderIso.addRight (-d)) '' S := by
      ext z
      constructor <;> tauto
    have hmap := (OrderIso.addRight (-d)).map_csInf' (entranceShift_cdf_superlevel_nonempty hμlarge hu1) (entranceShift_cdf_superlevel_bddBelow hμlarge hu hzeroLarge)
    have hmap' : sInf ((fun z : ℝ => z - d) '' S) = sInf S - d := by
      rw [himage, ← hmap, OrderIso.addRight_apply]
      ring
    unfold cdfGeneralizedQuantile
    rwa [hset]
  have hzeroShift (z : ℝ) (hz : z ≤ -d) : ProbabilityTheory.cdf μshift z = 0 := by
    rw [conditionedPositiveEntranceShiftedMeasure_cdf_eq_integral hb ht]
    have hzero : ∀ y, y ∈ Set.Iic z →
        conditionedPositiveEntranceDensity b t (y + d) = 0 := by
      intro y hy
      exact DOZZ.Proofs.conditionedPositiveEntranceDensity_eq_zero_of_nonpos hb ht (by
        change y ≤ z at hy
        linarith)
    rw [setIntegral_congr_fun measurableSet_Iic hzero]
    simp
  have hshiftBdd : BddBelow {z | u ≤ ProbabilityTheory.cdf μshift z} := by
    refine ⟨-d, ?_⟩
    intro z hz
    change u ≤ ProbabilityTheory.cdf μshift z at hz
    by_contra hnot
    rw [hzeroShift z (le_of_lt (lt_of_not_ge hnot))] at hz
    linarith
  have hqorder := cdfGeneralizedQuantile_antitone hcdfOrder hnonempty hshiftBdd
  rw [hquantShift] at hqorder
  nlinarith

end DOZZ.Proofs

end
