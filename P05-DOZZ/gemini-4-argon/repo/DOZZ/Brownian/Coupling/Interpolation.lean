/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.FiniteGrid

/-!
# Continuous interpolation of the shared entrance grids

Join the zero entrance point to the first sampled value, interpolate consecutive grid values,
and extend constantly beyond the last grid time. The construction uses continuous clipped ramps,
so measurability on the compact-open path carrier follows directly from evaluation measurability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- A clipped affine ramp joining zero at `a` to one at `a + δ`. -/
noncomputable def couplingRamp (a δ t : ℝ) : ℝ := min 1 (max 0 ((t - a) / δ))

theorem continuous_couplingRamp a δ : Continuous (couplingRamp a δ) := by
  unfold couplingRamp
  fun_prop

theorem couplingRamp_nonneg a δ t : 0 ≤ couplingRamp a δ t :=
  le_min zero_le_one (le_max_left _ _)

theorem couplingRamp_le_one a δ t : couplingRamp a δ t ≤ 1 := min_le_left _ _


theorem couplingRamp_eq_one {a δ t} (hδ : 0 < δ) (ht : a + δ ≤ t) :
    couplingRamp a δ t = 1 := by
  exact min_eq_left (((le_div_iff₀ hδ).mpr (by linarith)).trans (le_max_right _ _))


/-- Regard the ramp as an actual continuous path on nonnegative time. -/
noncomputable def couplingRampPath (a δ : ℝ) : BrownianPath :=
  ⟨fun t => couplingRamp a δ t, (continuous_couplingRamp a δ).comp NNReal.continuous_coe⟩

/-- Linearly interpolate positive finite entrance samples at times `(i+1)δ`. -/
noncomputable def couplingGridInterpolant (δ : ℝ) :
    (n : ℕ) → ConditionedEntranceGridPath n → BrownianPath
  | 0, x => (ContinuousMap.const _ (x 0).1) * couplingRampPath 0 δ
  | n + 1, x => couplingGridInterpolant δ n (Fin.init x) +
      (ContinuousMap.const _ ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1)) *
        couplingRampPath (((n : ℝ) + 1) * δ) δ

/-- The interpolated path depends measurably on every finite vector of sampled values. -/
theorem measurable_couplingGridInterpolant δ n :
    Measurable (couplingGridInterpolant δ n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  induction n with
  | zero =>
      change Measurable (fun x : ConditionedEntranceGridPath 0 =>
        (x 0).1 * couplingRamp 0 δ (t : ℝ))
      exact (measurable_subtype_coe.comp (measurable_pi_apply 0)).mul_const _
  | succ n ih =>
      change Measurable (fun x : ConditionedEntranceGridPath (n + 1) =>
        couplingGridInterpolant δ n (Fin.init x) t +
          ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) *
            couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ))
      exact (ih.comp (measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc)).add (((measurable_subtype_coe.comp
        (measurable_pi_apply (Fin.last (n + 1)))).sub
          (measurable_subtype_coe.comp (measurable_pi_apply (Fin.last n).castSucc))).mul_const _)

/-- Beyond the terminal grid time, the interpolant is exactly its last sampled value. -/
theorem couplingGridInterpolant_terminal {δ} (hδ : 0 < δ) (n : ℕ)
    x (t : ℝ≥0)
    (ht : ((n : ℝ) + 1) * δ ≤ (t : ℝ)) :
    couplingGridInterpolant δ n x t = (x (Fin.last n)).1 := by
  induction n with
  | zero =>
      change (x 0).1 * couplingRamp 0 δ (t : ℝ) = (x (Fin.last 0)).1
      rw [couplingRamp_eq_one hδ (by simpa using ht), mul_one]
      rfl
  | succ n ih =>
      change couplingGridInterpolant δ n (Fin.init x) t +
        ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) *
          couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
      rw [ih (Fin.init x) (show ((n : ℝ) + 1) * δ ≤ (t : ℝ) by push_cast at ht; nlinarith), (couplingRamp_eq_one hδ (by push_cast at ht; nlinarith)), mul_one]
      change (x (Fin.last n).castSucc).1 +
        ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) = _
      ring

/-- Before a new segment begins, appending it leaves the old interpolation unchanged. -/
theorem couplingGridInterpolant_before_append {δ} (hδ : 0 < δ) (n : ℕ)
    x (t : ℝ≥0)
    (ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ) :
    couplingGridInterpolant δ (n + 1) x t = couplingGridInterpolant δ n (Fin.init x) t := by
  have couplingRamp_eq_zero {a} {t} (ht : t ≤ a) : couplingRamp a δ t = 0 := by
    rw [couplingRamp, max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le)]
    norm_num
  change couplingGridInterpolant δ n (Fin.init x) t + _ *
    couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
  rw [couplingRamp_eq_zero ht, mul_zero, add_zero]

/-- On the new segment the interpolant is a convex combination of its two endpoint values. -/
theorem couplingGridInterpolant_after_append {δ} (hδ : 0 < δ) (n : ℕ)
    x (t : ℝ≥0)
    (ht : ((n : ℝ) + 1) * δ ≤ (t : ℝ)) :
    couplingGridInterpolant δ (n + 1) x t =
      (1 - couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ)) * (x (Fin.last n).castSucc).1 +
        couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) * (x (Fin.last (n + 1))).1 := by
  change couplingGridInterpolant δ n (Fin.init x) t + _ *
    couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
  rw [couplingGridInterpolant_terminal hδ n (Fin.init x) t ht]
  simp only [ContinuousMap.const_apply]
  change (x (Fin.last n).castSucc).1 +
    ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) *
      couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
  ring



/-- Reflect all finite-grid interpolants into the negative path convention. -/
noncomputable def couplingInterpolatedFamily {J : Type*} (δ : ℝ) (n : ℕ)
    (x : CoupledEntranceGridPath J n) : J → BrownianPath :=
  fun j => -(couplingGridInterpolant δ n (x j))

theorem measurable_couplingInterpolatedFamily {J : Type*} δ n :
    Measurable (couplingInterpolatedFamily (J := J) δ n) :=
  measurable_pi_iff.mpr fun j =>
    ((measurable_couplingGridInterpolant δ n).comp (measurable_pi_apply j)).neg


/-- The actual continuous-path joint grid law. -/
noncomputable def couplingInterpolatedGridMeasure {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : Measure (J → BrownianPath) :=
  (coupledEntranceGridMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n).map
    (couplingInterpolatedFamily δ n)

theorem couplingInterpolatedGridMeasure_isProbabilityMeasure {J : Type*}
    (v : J → ℝ≥0) δ (hδ : 0 < δ) n :
    IsProbabilityMeasure (couplingInterpolatedGridMeasure v δ hδ n) := by
  let _ := coupledEntranceGridMeasure_isProbabilityMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_couplingInterpolatedFamily δ n).aemeasurable).mpr inferInstance

/-- Continuous interpolation introduces no error into the full marginal finite-grid law. -/
theorem couplingInterpolatedGridMeasure_coordinate_map {J : Type*}
    (v : J → ℝ≥0) δ (hδ : 0 < δ) n j :
    (couplingInterpolatedGridMeasure v δ hδ n).map (fun F => F j) =
    (conditionedPositiveEntranceGridMeasure (v j) δ (fun _ => δ) (NNReal.coe_nonneg (v j))
      hδ (fun _ => hδ) n).map (fun x => -(couplingGridInterpolant δ n x)) := by
  rw [couplingInterpolatedGridMeasure, Measure.map_map (measurable_pi_apply j)
    (measurable_couplingInterpolatedFamily δ n)]
  change (coupledEntranceGridMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n).map
    ((fun x => -(couplingGridInterpolant δ n x)) ∘ (fun x => x j)) = _
  have hnegative : Measurable (fun x =>
      -(couplingGridInterpolant δ n x)) := (measurable_couplingGridInterpolant δ n).neg
  rw [← Measure.map_map hnegative (measurable_pi_apply j),
    coupledEntranceGridMeasure_coordinate_map]

/-- The common all-time order event is preserved by the actual interpolation pushforward. -/
theorem couplingInterpolatedGridMeasure_order_ae {J : Type*} [Countable J]
    (v : J → ℝ≥0) δ (hδ : 0 < δ) n :
    ∀ᵐ F ∂couplingInterpolatedGridMeasure v δ hδ n,
      F ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  have couplingRamp_time_budget {a} {t} (hat : a ≤ t) : couplingRamp a δ t * δ ≤ t - a := by
    rw [couplingRamp, max_eq_right (div_nonneg (sub_nonneg.mpr hat) hδ.le)]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hδ.le).trans_eq (div_mul_cancel₀ _ hδ.ne')
  have couplingInterpolatedFamily_mem_orderSet x (hx : x ∈ coupledEntranceGridOrderSet v δ (fun _ => δ) n) : couplingInterpolatedFamily δ n x ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
    have coupledEntranceGridTime_uniform δ (n : ℕ) : coupledEntranceGridTime δ (fun _ => δ) n = ((n : ℝ) + 1) * δ := by
      simp only [coupledEntranceGridTime, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have couplingGridInterpolant_order {d} (hd : 0 ≤ d) n x y (hxy : ∀ i : Fin (n + 1), (x i).1 ≤ (y i).1 ∧ (y i).1 ≤ (x i).1 + d * (((i.val : ℝ) + 1) * δ)) (t : ℝ≥0) : couplingGridInterpolant δ n x t ≤ couplingGridInterpolant δ n y t ∧ couplingGridInterpolant δ n y t ≤ couplingGridInterpolant δ n x t + d * (t : ℝ) := by
      induction n with
      | zero =>
          have hx0 := hxy 0
          have hramp0 := couplingRamp_nonneg 0 δ (t : ℝ)
          change (x 0).1 * couplingRamp 0 δ (t : ℝ) ≤
              (y 0).1 * couplingRamp 0 δ (t : ℝ) ∧
            (y 0).1 * couplingRamp 0 δ (t : ℝ) ≤
              (x 0).1 * couplingRamp 0 δ (t : ℝ) + d * (t : ℝ)
          have hupper := mul_le_mul_of_nonneg_right hx0.2 hramp0
          have hbudget' := mul_le_mul_of_nonneg_left (couplingRamp_time_budget t.2) hd
          simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul, sub_zero] at hupper hbudget'
          constructor
          · exact mul_le_mul_of_nonneg_right hx0.1 hramp0
          · calc
              _ ≤ ((x 0).1 + d * δ) * couplingRamp 0 δ (t : ℝ) := hupper
              _ = (x 0).1 * couplingRamp 0 δ (t : ℝ) +
                  d * (couplingRamp 0 δ (t : ℝ) * δ) := by ring
              _ ≤ _ := add_le_add_right hbudget' _
      | succ n ih =>
          by_cases ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ
          · rw [couplingGridInterpolant_before_append hδ n x t ht,
              couplingGridInterpolant_before_append hδ n y t ht]
            exact ih (Fin.init x) (Fin.init y) (fun i => hxy i.castSucc)
          · have ht' := (le_of_not_ge ht)
            rw [couplingGridInterpolant_after_append hδ n x t ht',
              couplingGridInterpolant_after_append hδ n y t ht']
            have hold := hxy (Fin.last n).castSucc
            have hnew := hxy (Fin.last (n + 1))
            simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] at hold hnew
            have := couplingRamp_nonneg (((n : ℝ) + 1) * δ) δ (t : ℝ)
            have := couplingRamp_le_one (((n : ℝ) + 1) * δ) δ (t : ℝ)
            have hbudget := couplingRamp_time_budget ht'
            constructor <;> nlinarith
    intro j k _ hjk t
    obtain ⟨hlo, hhi⟩ := couplingGridInterpolant_order (sub_nonneg.mpr hjk) n
      (x j) (x k) (by intro i; simpa only [coupledEntranceGridTime_uniform] using hx j k hjk i) t
    change -couplingGridInterpolant δ n (x k) t ≤ -couplingGridInterpolant δ n (x j) t ∧
      -couplingGridInterpolant δ n (x j) t ≤
        -couplingGridInterpolant δ n (x k) t + ((v k : ℝ) - (v j : ℝ)) * (t : ℝ)
    constructor <;> linarith
  apply (ae_map_iff (measurable_couplingInterpolatedFamily δ n).aemeasurable
    (isClosed_negativeEntranceOrderSet (fun j => (v j : ℝ))).measurableSet).mpr
  exact (coupledEntranceGridMeasure_order_ae v δ (fun _ => δ) hδ (fun _ => hδ) n).mono
    fun x hx => couplingInterpolatedFamily_mem_orderSet x hx

/-- The joint interpolation law in the probability-measure carrier used by Prokhorov. -/
noncomputable def couplingInterpolatedGridProbability {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ProbabilityMeasure (J → BrownianPath) :=
  ⟨couplingInterpolatedGridMeasure v δ hδ n,
    couplingInterpolatedGridMeasure_isProbabilityMeasure v δ hδ n⟩

end DOZZ.Proofs
