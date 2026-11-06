/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.PoleSubtractedObservable

/-!
# The pole-subtracted masses

Deterministic bookkeeping for [KRV, Lemma 10.3]. The two separated insertions `α₂ = 2/γ + η` at `2`
and `α₃ = 2/γ - η` at `-2` give the pole weight; the insertion `a` at `0` gives the zero tilt
`(|x|_+/|x|)^{γ a}`. The cutoff tilted mass `T_{a,n}` integrates their product over
`C_n = {|x| ≥ e^{-n}}`:

* `T_{0,n}` is the base mass `Z_{C_n}(0)` and the two unit balls carry the local mass;
* `T_{a,n}` increases to the total mass `Z_ℂ(a)` when the measure has no atom at `0`;
* the Cameron–Martin tilt by `a X_m(0)` multiplies the measure by `circleTiltDensity γ a m`,
  which is the zero tilt on `C_n` for `n ≤ m` and is `1` on `{|x| ≥ 1}`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The two-pole weight `(|x|_+/|x-2|)^{γα₂} (|x|_+/|x+2|)^{γα₃}`. -/
noncomputable def poleWeight (γ η : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.rpow (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x - (2 : ℂ)‖) (γ * (2 / γ + η)) *
    ENNReal.rpow (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x + (2 : ℂ)‖) (γ * (2 / γ - η))

/-- The zero tilt `(|x|_+/|x|)^{γ a}`. -/
noncomputable def zeroTilt (γ a : ℝ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.rpow (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x‖) (γ * a)

/-- The cutoff region `C_n = {|x| ≥ e^{-n}}`. -/
def cutoffRegion (n : ℕ) : Set ℂ := {x | Real.exp (-(n : ℝ)) ≤ ‖x‖}

/-- The two unit balls around the poles. -/
def poleBalls : Set ℂ := Metric.ball (2 : ℂ) 1 ∪ Metric.ball (-2 : ℂ) 1

/-- The cutoff tilted mass `T_{a,n} = ∫_{C_n} (|x|_+/|x|)^{γa} w(x) μ(dx)`. -/
noncomputable def cutoffTiltedMass (γ η a : ℝ) (n : ℕ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x in cutoffRegion n, zeroTilt γ a x * poleWeight γ η x ∂μ

/-- The density of the Cameron–Martin tilt by `a X_m(0)`:
`exp (γ a (log |x|_+ - log max(e^{-m}, |x|)))`. -/
noncomputable def circleTiltDensity (γ a : ℝ) (m : ℕ) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * (a * (Real.log (normPlus x) -
    Real.log (max (Real.exp (-(m : ℝ))) ‖x‖)))))

/-! ### Measurability -/

private theorem measurable_normPlus_aux : Measurable normPlus :=
  measurable_const.max measurable_norm

private theorem measurable_setLIntegral_measure {s} (hs : MeasurableSet s)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure ℂ => ∫⁻ x in s, f x ∂μ := by
  rw [(show (fun μ : Measure ℂ => ∫⁻ x in s, f x ∂μ) = fun μ : Measure ℂ => ∫⁻ x, s.indicator f x ∂μ by funext μ; exact (lintegral_indicator hs f).symm)]
  exact Measure.measurable_lintegral (hf.indicator hs)

theorem measurable_poleWeight γ η : Measurable (poleWeight γ η) := by
  have := measurable_normPlus_aux
  unfold poleWeight
  simp only [ENNReal.rpow_eq_pow]
  fun_prop

theorem measurable_zeroTilt γ a : Measurable (zeroTilt γ a) := by
  have := measurable_normPlus_aux
  unfold zeroTilt
  simp only [ENNReal.rpow_eq_pow]
  fun_prop

theorem measurable_circleTiltDensity γ a m :
    Measurable (circleTiltDensity γ a m) := by
  have := measurable_normPlus_aux
  unfold circleTiltDensity
  fun_prop

theorem measurableSet_cutoffRegion n : MeasurableSet (cutoffRegion n) :=
  (isClosed_le continuous_const continuous_norm).measurableSet

theorem measurableSet_poleBalls : MeasurableSet poleBalls :=
  Metric.isOpen_ball.measurableSet.union Metric.isOpen_ball.measurableSet

theorem measurable_cutoffTiltedMass γ η a n :
    Measurable fun μ : Measure ℂ => cutoffTiltedMass γ η a n μ :=
  measurable_setLIntegral_measure (measurableSet_cutoffRegion n)
    ((measurable_zeroTilt γ a).mul (measurable_poleWeight γ η))

theorem measurable_poleLocalMass γ η :
    Measurable fun μ : Measure ℂ => poleLocalMass γ (2 / γ + η) (2 / γ - η) μ := by
  unfold poleLocalMass
  exact Measure.measurable_lintegral
    (Measurable.ite measurableSet_poleBalls (measurable_poleWeight γ η) measurable_const)

theorem measurable_poleTotalMass γ η a :
    Measurable fun μ : Measure ℂ => poleTotalMass γ a (2 / γ + η) (2 / γ - η) μ := by
  have := measurable_normPlus_aux
  unfold poleTotalMass
  refine Measure.measurable_lintegral ?_
  simp only [ENNReal.rpow_eq_pow]
  fun_prop

/-! ### Regions -/

private theorem norm_two_aux : ‖(2 : ℂ)‖ = 2 := by simp

private theorem mem_ball_two_iff {x} {r} :
    x ∈ Metric.ball (2 : ℂ) r ↔ ‖x - 2‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm]

private theorem mem_ball_neg_two_iff {x} {r} :
    x ∈ Metric.ball (-2 : ℂ) r ↔ ‖x + 2‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add]

private theorem two_le_norm_add_norm_sub (x : ℂ) : 2 ≤ ‖x‖ + ‖x - 2‖ := by
  have h := norm_sub_le x (x - 2)
  rwa [sub_sub_cancel, norm_two_aux] at h






private theorem exp_neg_natCast_le_one (n : ℕ) : Real.exp (-(n : ℝ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  simp

private theorem norm_pos_of_mem_cutoffRegion {n} {x} (hx : x ∈ cutoffRegion n) :
    0 < ‖x‖ :=
  lt_of_lt_of_le (Real.exp_pos _) hx

theorem one_lt_norm_of_mem_poleBalls {x} (hx : x ∈ poleBalls) : 1 < ‖x‖ := by
  have two_le_norm_add_norm_add : 2 ≤ ‖x‖ + ‖x + 2‖ := by
    have h := norm_sub_le (x + 2) x
    rwa [add_sub_cancel_left, norm_two_aux, add_comm] at h
  rcases hx with h | h
  · linarith [mem_ball_two_iff.mp h, two_le_norm_add_norm_sub x]
  · linarith [mem_ball_neg_two_iff.mp h, two_le_norm_add_norm_add]


theorem cutoffRegion_mono : Monotone cutoffRegion := by
  intro n m hnm x hx
  have h : Real.exp (-(m : ℝ)) ≤ Real.exp (-(n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  exact h.trans hx



/-! ### The masses defined in the statements -/

theorem zeroTilt_zero γ x : zeroTilt γ 0 x = 1 := by
  unfold zeroTilt
  rw [mul_zero, ENNReal.rpow_eq_pow, ENNReal.rpow_zero]

theorem zeroTilt_of_one_le_norm γ a {x} (hx : 1 ≤ ‖x‖) : zeroTilt γ a x = 1 := by
  have h1 : normPlus x = ‖x‖ := max_eq_right hx
  have h0 : ENNReal.ofReal ‖x‖ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  unfold zeroTilt
  rw [h1, ENNReal.div_self h0 ENNReal.ofReal_ne_top, ENNReal.rpow_eq_pow, ENNReal.one_rpow]

theorem poleCutoffBaseMass_eq {Ω : Type*} [MeasurableSpace Ω] (M : Ω → Measure ℂ)
    γ η n ω :
    poleCutoffBaseMass M γ η n ω = cutoffTiltedMass γ η 0 n (M ω) := by
  unfold poleCutoffBaseMass cutoffTiltedMass
  rw [← lintegral_indicator (measurableSet_cutoffRegion n)]
  refine lintegral_congr fun x => ?_
  by_cases hx : Real.exp (-(n : ℝ)) ≤ ‖x‖
  · have hx' : x ∈ cutoffRegion n := hx
    simp [Set.indicator_of_mem hx', hx, zeroTilt_zero, poleWeight]
  · have hx' : x ∉ cutoffRegion n := hx
    simp [Set.indicator_of_notMem hx', hx]

theorem poleLocalMass_eq γ η (μ : Measure ℂ) :
    poleLocalMass γ (2 / γ + η) (2 / γ - η) μ = ∫⁻ x in poleBalls, poleWeight γ η x ∂μ := by
  unfold poleLocalMass
  rw [← lintegral_indicator measurableSet_poleBalls]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ poleBalls
  · have hx' : x ∈ Metric.ball (2 : ℂ) 1 ∨ x ∈ Metric.ball (-2 : ℂ) 1 := hx
    rw [Set.indicator_of_mem hx, ite_eq_left hx']
    rfl
  · have hx' : ¬ (x ∈ Metric.ball (2 : ℂ) 1 ∨ x ∈ Metric.ball (-2 : ℂ) 1) := hx
    rw [Set.indicator_of_notMem hx, ite_eq_right hx']

theorem poleTotalMass_eq γ η a (μ : Measure ℂ) :
    poleTotalMass γ a (2 / γ + η) (2 / γ - η) μ =
      ∫⁻ x, zeroTilt γ a x * poleWeight γ η x ∂μ := by
  unfold poleTotalMass
  refine lintegral_congr fun x => ?_
  unfold zeroTilt poleWeight
  rw [mul_assoc]

/-! ### Monotonicity, splitting and the limit -/

theorem cutoffTiltedMass_eq_localMass_add γ η a n (μ : Measure ℂ) :
    cutoffTiltedMass γ η a n μ = poleLocalMass γ (2 / γ + η) (2 / γ - η) μ +
      ∫⁻ x in cutoffRegion n \ poleBalls, zeroTilt γ a x * poleWeight γ η x ∂μ := by
  have poleBalls_subset_cutoffRegion : poleBalls ⊆ cutoffRegion n := fun _ hx =>
    (exp_neg_natCast_le_one n).trans (one_lt_norm_of_mem_poleBalls hx).le
  have hcongr : ∫⁻ x in poleBalls, poleWeight γ η x ∂μ =
      ∫⁻ x in poleBalls, zeroTilt γ a x * poleWeight γ η x ∂μ := by
    refine setLIntegral_congr_fun measurableSet_poleBalls (fun x hx => ?_)
    rw [zeroTilt_of_one_le_norm γ a (one_lt_norm_of_mem_poleBalls hx).le, one_mul]
  rw [poleLocalMass_eq, hcongr, ← lintegral_union
    ((measurableSet_cutoffRegion n).diff measurableSet_poleBalls) Set.disjoint_sdiff_right,
    Set.union_sdiff_cancel (poleBalls_subset_cutoffRegion)]
  rfl

theorem localMass_le_cutoffTiltedMass γ η a n (μ : Measure ℂ) :
    poleLocalMass γ (2 / γ + η) (2 / γ - η) μ ≤ cutoffTiltedMass γ η a n μ := by
  rw [cutoffTiltedMass_eq_localMass_add]
  exact le_self_add

theorem cutoffTiltedMass_succ γ η a n (μ : Measure ℂ) :
    cutoffTiltedMass γ η a (n + 1) μ = cutoffTiltedMass γ η a n μ +
      ∫⁻ x in cutoffRegion (n + 1) \ cutoffRegion n, zeroTilt γ a x * poleWeight γ η x ∂μ := by
  unfold cutoffTiltedMass
  rw [← lintegral_union
    ((measurableSet_cutoffRegion (n + 1)).diff (measurableSet_cutoffRegion n))
    Set.disjoint_sdiff_right, Set.union_sdiff_cancel (cutoffRegion_mono (Nat.le_succ n))]

theorem monotone_cutoffTiltedMass γ η a (μ : Measure ℂ) :
    Monotone fun n => cutoffTiltedMass γ η a n μ :=
  fun _ _ hnm => lintegral_mono_set (cutoffRegion_mono hnm)

theorem cutoffTiltedMass_le_totalMass γ η a n (μ : Measure ℂ) :
    cutoffTiltedMass γ η a n μ ≤ poleTotalMass γ a (2 / γ + η) (2 / γ - η) μ := by
  rw [poleTotalMass_eq]
  exact setLIntegral_le_lintegral _ _

theorem tendsto_cutoffTiltedMass γ η a (μ : Measure ℂ) (h0 : μ {0} = 0) :
    Tendsto (fun n => cutoffTiltedMass γ η a n μ) atTop
      (𝓝 (poleTotalMass γ a (2 / γ + η) (2 / γ - η) μ)) := by
  have iUnion_cutoffRegion : ⋃ n, cutoffRegion n = {0}ᶜ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩ hx0
      exact (norm_pos_iff.mp (norm_pos_of_mem_cutoffRegion hn)) hx0
    · intro hx0
      obtain ⟨n, hn⟩ := exists_nat_ge (-Real.log ‖x‖)
      refine ⟨n, ?_⟩
      change Real.exp (-(n : ℝ)) ≤ ‖x‖
      rw [← Real.le_log_iff_exp_le (norm_pos_iff.mpr hx0)]
      linarith
  have hFm : Measurable fun x => zeroTilt γ a x * poleWeight γ η x :=
    (measurable_zeroTilt γ a).mul (measurable_poleWeight γ η)
  have hae : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa using h0
  have hsup : poleTotalMass γ a (2 / γ + η) (2 / γ - η) μ =
      ⨆ n, cutoffTiltedMass γ η a n μ := by
    have h1 : ∀ n, cutoffTiltedMass γ η a n μ = ∫⁻ x, (cutoffRegion n).indicator
        (fun x => zeroTilt γ a x * poleWeight γ η x) x ∂μ := fun n =>
      (lintegral_indicator (measurableSet_cutoffRegion n) _).symm
    simp_rw [h1]
    rw [← lintegral_iSup (fun n => hFm.indicator (measurableSet_cutoffRegion n)) (fun n m hnm x =>
      Set.indicator_le_indicator_of_subset (cutoffRegion_mono hnm) (fun _ => zero_le) x),
      poleTotalMass_eq]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨N, hN⟩ : ∃ N, x ∈ cutoffRegion N := by
      have : x ∈ ⋃ n, cutoffRegion n := by
        rw [iUnion_cutoffRegion]
        exact hx
      simpa using this
    refine le_antisymm (le_iSup_of_le N ?_) (iSup_le fun n => Set.indicator_le_self' ?_ x)
    · rw [Set.indicator_of_mem hN]
    · exact fun _ _ => zero_le
  rw [hsup]
  exact tendsto_atTop_iSup (monotone_cutoffTiltedMass γ η a μ)

/-! ### The circle tilt -/



theorem cutoffTiltedMass_withDensity γ η a {n m} (hnm : n ≤ m) (μ : Measure ℂ) :
    cutoffTiltedMass γ η 0 n (μ.withDensity (circleTiltDensity γ a m)) =
      cutoffTiltedMass γ η a n μ := by
  have circleTiltDensity_eq_zeroTilt {x} (hx : x ∈ cutoffRegion n) : circleTiltDensity γ a m x = zeroTilt γ a x := by
    have hpos := norm_pos_of_mem_cutoffRegion hx
    have hnp : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left _ _)
    unfold circleTiltDensity zeroTilt
    rw [max_eq_right (cutoffRegion_mono hnm hx), ← ENNReal.ofReal_div_of_pos hpos, ENNReal.rpow_eq_pow,
      ENNReal.ofReal_rpow_of_pos (div_pos hnp hpos), Real.rpow_def_of_pos (div_pos hnp hpos),
      Real.log_div hnp.ne' hpos.ne']
    congr 2
    ring
  have hg : Measurable fun x => zeroTilt γ 0 x * poleWeight γ η x :=
    (measurable_zeroTilt γ 0).mul (measurable_poleWeight γ η)
  unfold cutoffTiltedMass
  rw [setLIntegral_withDensity_eq_setLIntegral_mul μ (measurable_circleTiltDensity γ a m)
    hg (measurableSet_cutoffRegion n)]
  refine setLIntegral_congr_fun (measurableSet_cutoffRegion n) (fun x hx => ?_)
  simp only [Pi.mul_apply]
  rw [circleTiltDensity_eq_zeroTilt hx, zeroTilt_zero, one_mul]

theorem poleLocalMass_withDensity γ η a m (μ : Measure ℂ) :
    poleLocalMass γ (2 / γ + η) (2 / γ - η) (μ.withDensity (circleTiltDensity γ a m)) =
      poleLocalMass γ (2 / γ + η) (2 / γ - η) μ := by
  have circleTiltDensity_of_one_le_norm {x} (hx : 1 ≤ ‖x‖) : circleTiltDensity γ a m x = 1 := by
    unfold circleTiltDensity
    rw [max_eq_right ((exp_neg_natCast_le_one m).trans hx), show normPlus x = ‖x‖ from max_eq_right hx]
    simp
  rw [poleLocalMass_eq, poleLocalMass_eq,
    setLIntegral_withDensity_eq_setLIntegral_mul μ (measurable_circleTiltDensity γ a m)
      (measurable_poleWeight γ η) measurableSet_poleBalls]
  refine setLIntegral_congr_fun measurableSet_poleBalls (fun x hx => ?_)
  simp only [Pi.mul_apply]
  rw [circleTiltDensity_of_one_le_norm (one_lt_norm_of_mem_poleBalls hx).le, one_mul]

/-! ### Pointwise bounds -/

private theorem ratio_le_three {t u} (hu : 0 < u) (h : t ≤ 3 * u) :
    ENNReal.ofReal t / ENNReal.ofReal u ≤ 3 := by
  rw [← ENNReal.ofReal_div_of_pos hu]
  calc ENNReal.ofReal (t / u) ≤ ENNReal.ofReal 3 :=
        ENNReal.ofReal_le_ofReal ((div_le_iff₀ hu).mpr h)
    _ = 3 := by simp

private theorem one_le_ratio {t u} (ht : 0 < t) (h : u ≤ t) :
    1 ≤ ENNReal.ofReal t / ENNReal.ofReal u := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr (ENNReal.ofReal_pos.mpr ht).ne')
    (Or.inl ENNReal.ofReal_ne_top), one_mul]
  exact ENNReal.ofReal_le_ofReal h


private theorem exponent_add {γ η : ℝ} (hγ : 0 < γ) : γ * (2 / γ + η) = 2 + γ * η := by
  field_simp

private theorem exponent_sub {γ η : ℝ} (hγ : 0 < γ) : γ * (2 / γ - η) = 2 - γ * η := by
  field_simp

private theorem mul_le_two {γ η : ℝ} (hγ : 0 < γ) (hηγ : η ≤ 2 / γ) : γ * η ≤ 2 := by
  calc γ * η ≤ γ * (2 / γ) := mul_le_mul_of_nonneg_left hηγ hγ.le
    _ = 2 := by field_simp

/-- Off the two balls the pole weight is at most `3^{γα₂} 3^{γα₃} = 81`. -/
theorem poleWeight_le_of_notMem_poleBalls {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hηγ : η ≤ 2 / γ) {x} (hx : x ∉ poleBalls) : poleWeight γ η x ≤ 81 := by
  have norm_le_norm_add_add : ‖x‖ ≤ ‖x + 2‖ + 2 := by
    have h := norm_sub_le (x + 2) 2
    rwa [add_sub_cancel_right, norm_two_aux] at h
  have norm_le_norm_sub_add : ‖x‖ ≤ ‖x - 2‖ + 2 := by
    have h := norm_add_le (x - 2) 2
    rwa [sub_add_cancel, norm_two_aux] at h
  have : 1 ≤ ‖x - 2‖ := by
    by_contra h
    exact hx (Or.inl (mem_ball_two_iff.mpr (not_le.mp h)))
  have : 1 ≤ ‖x + 2‖ := by
    by_contra h
    exact hx (Or.inr (mem_ball_neg_two_iff.mpr (not_le.mp h)))
  have := mul_le_two hγ hηγ
  have := mul_nonneg hγ.le hη
  unfold poleWeight
  simp only [ENNReal.rpow_eq_pow, exponent_add hγ, exponent_sub hγ]
  calc _ ≤ (3 : ℝ≥0∞) ^ (2 + γ * η) * (3 : ℝ≥0∞) ^ (2 - γ * η) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (ratio_le_three (by linarith) (max_le (by linarith) (by linarith [norm_le_norm_sub_add]))) (by linarith))
          (ENNReal.rpow_le_rpow (ratio_le_three (by linarith) (max_le (by linarith) (by linarith [norm_le_norm_add_add]))) (by linarith))
    _ = (3 : ℝ≥0∞) ^ ((2 + γ * η) + (2 - γ * η)) :=
        (ENNReal.rpow_add _ _ (by norm_num) (by norm_num)).symm
    _ = 81 := by
      rw [show (2 + γ * η) + (2 - γ * η) = ((4 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.rpow_natCast]
      norm_num

/-- On `B(2, 1/2)` the pole weight is at least `3^{-2}`. -/
theorem poleWeight_ge_of_mem_ball_two {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hηγ : η ≤ 2 / γ) {x : ℂ} (hx : x ∈ Metric.ball (2 : ℂ) (1 / 2)) :
    (1 / 9 : ℝ≥0∞) ≤ poleWeight γ η x := by
  have le_ratio {c} {t} {u} (hu : 0 < u) (h : c * u ≤ t) : ENNReal.ofReal c ≤ ENNReal.ofReal t / ENNReal.ofReal u := by
    rw [← ENNReal.ofReal_div_of_pos hu]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hu).mpr h)
  have norm_add_le_norm_sub_add : ‖x + 2‖ ≤ ‖x - 2‖ + 4 := by
    have h := norm_add_le (x - 2) 4
    rwa [(show x - 2 + 4 = x + 2 by ring), (show ‖(4 : ℂ)‖ = 4 by simp)] at h
  have four_le_norm_add_add_norm_sub : 4 ≤ ‖x + 2‖ + ‖x - 2‖ := by
    have h := norm_sub_le (x + 2) (x - 2)
    rwa [(show x + 2 - (x - 2) = 4 by ring), (show ‖(4 : ℂ)‖ = 4 by simp)] at h
  have := mem_ball_two_iff.mp hx
  have : 3 / 2 ≤ ‖x‖ := by linarith [two_le_norm_add_norm_sub x]
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith)
  have : ‖x + 2‖ ≤ 9 / 2 := by linarith [norm_add_le_norm_sub_add]
  have := mul_le_two hγ hηγ
  have := mul_nonneg hγ.le hη
  unfold poleWeight
  simp only [ENNReal.rpow_eq_pow, exponent_add hγ, exponent_sub hγ]
  calc (1 / 9 : ℝ≥0∞) = 1 ^ (2 + γ * η) * (ENNReal.ofReal (1 / 3)) ^ (2 : ℝ) := by
        rw [ENNReal.one_rpow, (show (ENNReal.ofReal (1 / 3)) ^ (2 : ℝ) = 1 / 9 by rw [ENNReal.ofReal_rpow_of_pos (by norm_num), Real.rpow_two, show ((1 : ℝ) / 3) ^ 2 = 1 / 9 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num)]; simp), one_mul]
    _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow (one_le_ratio (by rw [hnp]; linarith) (by rw [hnp]; linarith)) (by linarith))
        ((ENNReal.rpow_le_rpow_of_exponent_ge (ENNReal.ofReal_le_one.mpr (by norm_num))
          (by linarith)).trans (ENNReal.rpow_le_rpow (le_ratio (show 0 < ‖x + 2‖ by linarith [four_le_norm_add_add_norm_sub]) (by rw [hnp]; linarith)) (by linarith)))

/-- A nonpositive zero charge gives a tilt at most `1`. -/
theorem zeroTilt_le_one {γ a} (hγ : 0 < γ) (ha : a ≤ 0) x : zeroTilt γ a x ≤ 1 := by
  unfold zeroTilt
  rw [ENNReal.rpow_eq_pow]
  rcases (show γ * a ≤ 0 by nlinarith).lt_or_eq with h | h
  · exact ENNReal.rpow_le_one_of_one_le_of_neg (one_le_ratio (lt_of_lt_of_le one_pos (le_max_left _ _)) (le_max_right _ _)) h
  · rw [h, ENNReal.rpow_zero]

/-- On `C_n` a nonnegative zero charge gives a tilt at most `e^{γ a n}`. -/
theorem zeroTilt_le_of_mem_cutoffRegion {γ a} (hγ : 0 < γ) (ha : 0 ≤ a) {n} {x}
    (hx : x ∈ cutoffRegion n) : zeroTilt γ a x ≤ ENNReal.ofReal (Real.exp (γ * a * n)) := by
  have hpos := norm_pos_of_mem_cutoffRegion hx
  have := Real.one_le_exp (Nat.cast_nonneg n)
  have hratio : ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x‖ ≤
      ENNReal.ofReal (Real.exp n) := by
    rw [← ENNReal.ofReal_div_of_pos hpos]
    refine ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpos).mpr (max_le ?_ ?_))
    · calc (1 : ℝ) = Real.exp n * Real.exp (-(n : ℝ)) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp n * ‖x‖ := mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
    · nlinarith
  unfold zeroTilt
  rw [ENNReal.rpow_eq_pow]
  calc _ ≤ ENNReal.ofReal (Real.exp n) ^ (γ * a) :=
        ENNReal.rpow_le_rpow hratio (mul_nonneg hγ.le ha)
    _ = ENNReal.ofReal (Real.exp n ^ (γ * a)) := ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)
    _ = ENNReal.ofReal (Real.exp (γ * a * n)) := by
      rw [← Real.exp_mul]
      ring_nf

/-- Inside the unit disk the zero tilt is the weighted-ball weight `|x|^{-γa}`. -/
theorem zeroTilt_of_norm_lt_one γ a {x} (hx : ‖x‖ < 1) :
    zeroTilt γ a x = ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a) := by
  have h1 : normPlus x = 1 := max_eq_left hx.le
  unfold zeroTilt
  rw [h1, ENNReal.ofReal_one, ENNReal.rpow_eq_pow, ENNReal.rpow_eq_pow, neg_mul,
    ENNReal.rpow_neg, one_div, ENNReal.inv_rpow]

end DOZZ.Proofs

end
