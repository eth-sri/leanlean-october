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

theorem continuous_couplingRamp (a δ : ℝ) : Continuous (couplingRamp a δ) := by
  unfold couplingRamp
  fun_prop
section
variable (a δ t : ℝ)

theorem couplingRamp_nonneg : 0 ≤ couplingRamp a δ t :=
  le_min zero_le_one (le_max_left ..)

theorem couplingRamp_le_one : couplingRamp a δ t ≤ 1 := min_le_left ..

end
section
variable {a δ t : ℝ}
section
variable (hδ : 0 < δ)
include hδ

theorem couplingRamp_eq_zero (ht : t ≤ a) :
    couplingRamp a δ t = 0 := by
  rw [couplingRamp, max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le)]
  norm_num

theorem couplingRamp_eq_one (ht : a + δ ≤ t) :
    couplingRamp a δ t = 1 := by
  have hdiv : 1 ≤ (t - a) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  exact min_eq_left (hdiv.trans (le_max_right ..))

/-- The ramp's contribution to elapsed time never exceeds the elapsed time itself. -/
theorem couplingRamp_time_budget (hat : a ≤ t) :
    couplingRamp a δ t * δ ≤ t - a := by
  rw [couplingRamp, max_eq_right (div_nonneg (sub_nonneg.mpr hat) hδ.le)]
  exact (mul_le_mul_of_nonneg_right (min_le_right ..) hδ.le).trans_eq (div_mul_cancel₀ _ hδ.ne')

end

end

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
theorem measurable_couplingGridInterpolant (δ : ℝ) (n : ℕ) :
    Measurable (couplingGridInterpolant δ n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  induction n with
  | zero =>
      change Measurable (fun x : ConditionedEntranceGridPath 0 =>
        (x 0).1 * couplingRamp 0 δ t)
      exact (measurable_subtype_coe.comp (measurable_pi_apply 0)).mul_const _
  | succ n ih =>
      have hinit : Measurable (Fin.init : ConditionedEntranceGridPath (n + 1) →
          ConditionedEntranceGridPath n) :=
        by fun_prop
      change Measurable (fun x : ConditionedEntranceGridPath (n + 1) =>
        couplingGridInterpolant δ n (Fin.init x) t +
          ((x _).1 - (x (Fin.last n).castSucc).1) *
            couplingRamp _ δ t)
      exact (ih.comp hinit).add (((measurable_subtype_coe.comp
        (measurable_pi_apply _)).sub
          (measurable_subtype_coe.comp (measurable_pi_apply (Fin.last n).castSucc))).mul_const _)
section
variable {δ : ℝ}

/-- Beyond the terminal grid time, the interpolant is exactly its last sampled value. -/
theorem couplingGridInterpolant_terminal (hδ : 0 < δ) (n : ℕ)
    (x : ConditionedEntranceGridPath n) (t : ℝ≥0)
    (ht : ((n : ℝ) + 1) * δ ≤ (t : ℝ)) :
    couplingGridInterpolant δ n x t = (x (Fin.last n)).1 := by
  induction n with
  | zero =>
      change (x 0).1 * couplingRamp 0 δ t = (x (Fin.last 0)).1
      rw [couplingRamp_eq_one hδ (by simp_all), mul_one]
      rfl
  | succ n ih =>
      have hprev : (n + 1) * δ ≤ t := by
        grind
      have hramp : couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = 1 :=
        couplingRamp_eq_one hδ (by grind)
      change couplingGridInterpolant δ n (Fin.init x) t +
        ((x _).1 - (x (Fin.last n).castSucc).1) *
          couplingRamp _ δ t = _
      rw [ih (Fin.init x) hprev, hramp, mul_one]
      change (x (Fin.last n).castSucc).1 +
        ((x _).1 - (x (Fin.last n).castSucc).1) = _
      ring
section
variable (hδ : 0 < δ) (n : ℕ) (x : ConditionedEntranceGridPath (n + 1)) (t : ℝ≥0)
include hδ

/-- Before a new segment begins, appending it leaves the old interpolation unchanged. -/
theorem couplingGridInterpolant_before_append (ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ) :
    couplingGridInterpolant δ (n + 1) x t = couplingGridInterpolant δ n (Fin.init x) t := by
  change couplingGridInterpolant δ n (Fin.init x) t + _ *
    couplingRamp _ δ t = _
  rw [couplingRamp_eq_zero hδ ht, mul_zero, add_zero]

/-- On the new segment the interpolant is a convex combination of its two endpoint values. -/
theorem couplingGridInterpolant_after_append (ht : ((n : ℝ) + 1) * δ ≤ (t : ℝ)) :
    couplingGridInterpolant δ (n + 1) x t =
      (1 - couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ)) * (x (Fin.last n).castSucc).1 +
        couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) * (x (Fin.last (n + 1))).1 := by
  change couplingGridInterpolant δ n (Fin.init x) t + _ *
    couplingRamp _ δ t = _
  rw [couplingGridInterpolant_terminal hδ n (Fin.init x) t ht]
  simp
  change (x (Fin.last n).castSucc).1 +
    ((x _).1 - (x (Fin.last n).castSucc).1) *
      couplingRamp _ δ t = _
  ring

end

end

/-- Grid interpolation preserves the two quantitative drift inequalities at every real time. -/
theorem couplingGridInterpolant_order {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (n : ℕ) (x y : ConditionedEntranceGridPath n)
    (hxy : ∀ i : Fin (n + 1), (x i).1 ≤ (y i).1 ∧
      (y i).1 ≤ (x i).1 + d * (((i.val : ℝ) + 1) * δ))
    (t : ℝ≥0) : couplingGridInterpolant δ n x t ≤ couplingGridInterpolant δ n y t ∧
      couplingGridInterpolant δ n y t ≤ couplingGridInterpolant δ n x t + d * (t : ℝ) := by
  induction n with
  | zero =>
      have hx0 := hxy 0
      have hramp0 := couplingRamp_nonneg 0 δ t
      change (x 0).1 * couplingRamp 0 δ t ≤
          (y 0).1 * couplingRamp 0 δ t ∧
        (y 0).1 * couplingRamp 0 δ t ≤
          (x 0).1 * couplingRamp 0 δ t + d * t
      have hupper := mul_le_mul_of_nonneg_right hx0.2 hramp0
      have hbudget' := mul_le_mul_of_nonneg_left (couplingRamp_time_budget hδ t.2) hd
      simp at hupper hbudget'
      constructor
      · nlinarith
      · linarith
  | succ n ih =>
      by_cases ht : t ≤ (n + 1) * δ
      · rw [couplingGridInterpolant_before_append hδ n x t ht,
          couplingGridInterpolant_before_append hδ n y t ht]
        exact ih (Fin.init x) (Fin.init y) (fun i => hxy i.castSucc)
      · have ht' := (le_of_not_ge ht)
        rw [couplingGridInterpolant_after_append hδ n x t ht',
          couplingGridInterpolant_after_append hδ n y t ht']
        have hold := hxy (Fin.last n).castSucc
        have hnew := hxy (Fin.last (n + 1))
        simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] at hold hnew
        have hramp0 := couplingRamp_nonneg ((n + 1) * δ) δ t
        have hramp1 := couplingRamp_le_one ((n + 1) * δ) δ t
        have hlold := mul_le_mul_of_nonneg_left hold.1 (sub_nonneg.mpr hramp1)
        have hlnew := mul_le_mul_of_nonneg_left hnew.1 hramp0
        have huold := mul_le_mul_of_nonneg_left hold.2 (sub_nonneg.mpr hramp1)
        have hunew := mul_le_mul_of_nonneg_left hnew.2 hramp0
        have hbudget' := mul_le_mul_of_nonneg_left (couplingRamp_time_budget hδ ht') hd
        constructor <;> nlinarith

/-- Uniform-grid elapsed times match the affine interpolation endpoints exactly. -/
theorem coupledEntranceGridTime_uniform (δ : ℝ) (n : ℕ) :
    coupledEntranceGridTime δ (fun _ => δ) n = ((n : ℝ) + 1) * δ := by
  simp only [coupledEntranceGridTime, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Reflect all finite-grid interpolants into the negative path convention. -/
noncomputable def couplingInterpolatedFamily {J : Type*} (δ : ℝ) (n : ℕ)
    (x : CoupledEntranceGridPath J n) : J → BrownianPath :=
  fun j => -(couplingGridInterpolant δ n (x j))
section
variable {J : Type*}

theorem measurable_couplingInterpolatedFamily (δ : ℝ) (n : ℕ) :
    Measurable (couplingInterpolatedFamily (J := J) δ n) :=
  measurable_pi_iff.mpr fun j =>
    ((measurable_couplingGridInterpolant δ n).comp (measurable_pi_apply j)).neg

/-- Simultaneous grid order yields simultaneous continuous-path order, at every time. -/
theorem couplingInterpolatedFamily_mem_orderSet (v : J → ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : CoupledEntranceGridPath J n)
    (hx : x ∈ coupledEntranceGridOrderSet v δ (fun _ => δ) n) :
    couplingInterpolatedFamily δ n x ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  intro j k _ hjk t
  have hxy : ∀ i : Fin (n + 1), (x j i).1 ≤ (x k i).1 ∧
      (x k i).1 ≤ (x j i).1 + ((v k) - (v j)) * ((i.val + 1) * δ) := by
    intro i
    simpa only [coupledEntranceGridTime_uniform] using hx j k hjk i
  obtain ⟨hlo, hhi⟩ := couplingGridInterpolant_order hδ (sub_nonneg.mpr hjk) n
    (x j) (x k) hxy t
  change -couplingGridInterpolant δ n (x k) t ≤ -couplingGridInterpolant δ n (x j) t ∧
    -couplingGridInterpolant δ n (x j) t ≤
      -couplingGridInterpolant δ n (x k) t + ((v k) - (v j)) * t
  grind

end

/-- The actual continuous-path joint grid law. -/
noncomputable def couplingInterpolatedGridMeasure {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : Measure (J → BrownianPath) :=
  (coupledEntranceGridMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n).map
    (couplingInterpolatedFamily δ n)
section
variable {J : Type*}
section
variable (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)

theorem couplingInterpolatedGridMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (couplingInterpolatedGridMeasure v δ hδ n) := by
  let _ := coupledEntranceGridMeasure_isProbabilityMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_couplingInterpolatedFamily δ n).aemeasurable).mpr inferInstance

/-- Continuous interpolation introduces no error into the full marginal finite-grid law. -/
theorem couplingInterpolatedGridMeasure_coordinate_map (j : J) :
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

end

/-- The common all-time order event is preserved by the actual interpolation pushforward. -/
theorem couplingInterpolatedGridMeasure_order_ae [Countable J]
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∀ᵐ F ∂couplingInterpolatedGridMeasure v δ hδ n,
      F ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  apply (ae_map_iff (measurable_couplingInterpolatedFamily δ n).aemeasurable
    (isClosed_negativeEntranceOrderSet (fun j => (v j))).measurableSet).mpr
  exact (coupledEntranceGridMeasure_order_ae v δ (fun _ => δ) hδ (fun _ => hδ) n).mono
    fun x hx => couplingInterpolatedFamily_mem_orderSet v hδ n x hx

end

/-- The joint interpolation law in the probability-measure carrier used by Prokhorov. -/
noncomputable def couplingInterpolatedGridProbability {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ProbabilityMeasure (J → BrownianPath) :=
  ⟨couplingInterpolatedGridMeasure v δ hδ n,
    couplingInterpolatedGridMeasure_isProbabilityMeasure v δ hδ n⟩

end DOZZ.Proofs
