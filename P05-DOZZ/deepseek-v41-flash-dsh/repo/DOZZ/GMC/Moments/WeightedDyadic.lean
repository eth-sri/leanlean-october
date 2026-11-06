/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.Filter.AtTopBot.Ring
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Order.Monotone
public import DOZZ.Statements.GMC.WeightedGmcBallMass
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.SubunitSet
public import DOZZ.GMC.Moments.WeightedExponent

/-! Countable subadditivity for nonnegative powers at orders at most one. -/

@[expose] public section

open Filter
open MeasureTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Every positive radius strictly inside a reference disk lies in one dyadic shell. -/
theorem exists_dyadic_shell_index {R d : ℝ}
    (hd : 0 < d) (hdR : d < R) :
    ∃ n : ℕ, R / (2 : ℝ) ^ (n + 1) ≤ d ∧ d < R / (2 : ℝ) ^ n := by
  let q : ℝ := R / d
  have hq : 1 < q := by
    dsimp [q]
    exact (one_lt_div hd).2 hdR
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop := by
    have h := (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    exact h.congr' (Eventually.of_forall fun n => Real.rpow_natCast 2 n)
  have hexists : ∃ n : ℕ, q ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.mp hpow) q
    exact ⟨n, hn n le_rfl⟩
  let n : ℕ := Nat.find hexists
  have hqpow : q ≤ (2 : ℝ) ^ n := Nat.find_spec hexists
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0, pow_zero] at hqpow
    linarith
  have hprev : (2 : ℝ) ^ (n - 1) < q := by
    apply lt_of_not_ge
    intro h
    have hmin := Nat.find_min' hexists h
    omega
  refine ⟨n - 1, ?_, ?_⟩
  · have hqmul : R ≤ (2 : ℝ) ^ n * d := by
      dsimp [q] at hqpow
      exact (div_le_iff₀ hd).mp hqpow
    have htwopow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hbound : R / (2 : ℝ) ^ n ≤ d := (div_le_iff₀ (by positivity)).2 (by
      rw [htwopow] at hqmul ⊢
      linarith only [hqmul])
    have hindex : (n - 1) + 1 = n := by omega
    simpa [hindex] using hbound
  · have hprev' : (2 : ℝ) ^ (n - 1) * d < R := by
      dsimp [q] at hprev
      exact (lt_div_iff₀ hd).mp hprev
    have hbound : d < R / (2 : ℝ) ^ (n - 1) :=
      (lt_div_iff₀ (by positivity)).2 (by linarith only [hprev'])
    simpa using hbound

private theorem ennreal_ofReal_rpow_of_pos {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  have hleft : ENNReal.rpow (ENNReal.ofReal x) p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hx)) ENNReal.ofReal_ne_top
  have hright : ENNReal.ofReal (x ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal =
        (ENNReal.ofReal x).toReal ^ p := (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal := by
        rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)]

private theorem ennreal_rpow_finset_sum_le_tsum_rpow
    {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, a i) ^ p ≤ ∑ i ∈ s, (a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp]
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      exact ENNReal.rpow_add_le_add_rpow (a i) (∑ j ∈ s, a j) hp.le hp1 |>.trans
        (add_le_add_right ih _)

/-- For `0 < p ≤ 1`, the `p`th power of a countable sum is bounded by the sum of the `p`th
powers. -/
theorem ennreal_rpow_tsum_le_tsum_rpow
    {ι : Type*} [Countable ι] (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, a i) ^ p ≤ ∑' i, (a i) ^ p := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.tsum_eq_iSup_sum]
  have hmono : Monotone (fun x : ℝ≥0∞ => x ^ p) := fun _ _ h =>
    ENNReal.rpow_le_rpow h hp.le
  have hzero : (0 : ℝ≥0∞) ^ p = 0 := ENNReal.zero_rpow_of_pos hp
  have hcontinuous : Continuous (fun x : ℝ≥0∞ => x ^ p) :=
    ENNReal.continuous_rpow_const
  rw [hmono.map_iSup_of_continuousAt
    hcontinuous.continuousAt hzero]
  apply iSup_le
  intro s
  exact (ennreal_rpow_finset_sum_le_tsum_rpow s a hp hp1).trans
    (le_iSup_of_le s le_rfl)

/-- Every `0 < γ < 2` admits a positive subunit order strictly below the root insertion
threshold. -/
theorem exists_subunit_order_below_gamma_insertion {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      p < min (4 / γ ^ 2) (2 / γ * (Q γ - γ)) := by
  have hQ : 0 < Q γ - γ := by
    dsimp [Q]
    have hγsq : γ ^ 2 < 4 := by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
    field_simp [ne_of_gt hγ]
    linarith only [hγsq]
  let s : ℝ := 2 / γ * (Q γ - γ)
  let b : ℝ := min 1 s
  have hb : 0 < b := by positivity
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbs : b ≤ s := min_le_right _ _
  let p : ℝ := b / 2
  have hp : 0 < p := by positivity
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hpin : p < s := by dsimp [p]; linarith
  have hbulk : 1 < 4 / γ ^ 2 := by
    have hγsq : γ ^ 2 < 4 := by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
    rw [one_lt_div (sq_pos_of_pos hγ)]
    linarith only [hγsq]
  refine ⟨p, hp, hp1, ?_⟩
  rw [lt_min_iff]
  exact ⟨(lt_of_le_of_lt hp1 hbulk), by simpa [s] using hpin⟩

/-- A dyadic shell bound for a positive insertion charge. The coefficient is evaluated at the
inner edge of the shell, where the negative radial power is largest. -/
theorem weightedGmcBallMass_root_le_dyadic_charge
    (μ : Measure ℂ) (γ α R : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    weightedGmcBallMass γ μ α 0 R ≤
      ∑' n : ℕ,
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
          μ (Metric.ball 0 (R / (2 : ℝ) ^ n)) := by
  let B : Set ℂ := Metric.ball 0 R
  let density : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * α)
  let coverTerm : ℕ → ℂ → ℝ≥0∞ := fun n x =>
    (Metric.ball 0 (R / (2 : ℝ) ^ n)).indicator (fun _ =>
      ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) x
  have hpowerNeg : -γ * α < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hγ) hα
  have hpoint (x : ℂ) : B.indicator density x ≤ ∑' n : ℕ, coverTerm n x := by
    by_cases hx : x ∈ B
    · have hxR : ‖x‖ < R := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hx
      by_cases hzero : x = 0
      · subst x
        have hcoef (n : ℕ) : 1 ≤ ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) := by
          have hradle : R / (2 : ℝ) ^ (n + 1) ≤ 1 := by
            calc
              R / (2 : ℝ) ^ (n + 1) ≤ R := by
                apply (div_le_iff₀ (by positivity)).2
                calc
                  R = R * 1 := by ring
                  _ ≤ R * (2 : ℝ) ^ (n + 1) :=
                    mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le
              _ ≤ 1 := hR1
          have hbase : ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1)) ≤ 1 :=
            ENNReal.ofReal_le_one.mpr hradle
          calc
            1 = (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) ^ 0 := by simp
            _ ≤ (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) ^ (-γ * α) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hbase (by linarith)
        have hsumLower : (∑' _n : ℕ, (1 : ℝ≥0∞)) ≤
            ∑' n : ℕ, coverTerm n 0 := ENNReal.tsum_le_tsum fun n => by
          have hball : (0 : ℂ) ∈ Metric.ball 0 (R / (2 : ℝ) ^ n) := by
            simp only [Metric.mem_ball, dist_self]
            positivity
          simpa [coverTerm, hball] using hcoef n
        have hsum : ∑' n : ℕ, coverTerm n 0 = ⊤ := by
          have hsumConst : (⊤ : ℝ≥0∞) = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero).symm
          exact top_unique (hsumConst.symm ▸ hsumLower)
        have hleft : B.indicator density 0 = ⊤ := by
          have hball : (0 : ℂ) ∈ B := by simpa [B, Metric.mem_ball] using hR
          rw [Set.indicator_of_mem hball]
          change ENNReal.rpow (ENNReal.ofReal ‖(0 : ℂ)‖) (-γ * α) = ⊤
          simpa using (ENNReal.zero_rpow_of_neg hpowerNeg)
        rw [hleft, hsum]
      · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hzero
        obtain ⟨n, hlo, hhi⟩ := exists_dyadic_shell_index hnorm hxR
        have hlowpos : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
        have hpow : ‖x‖ ^ (-γ * α) ≤
            (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α) :=
          Real.rpow_le_rpow_of_nonpos hlowpos hlo (by linarith)
        have hden : density x ≤ ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) := by
          change ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * α) ≤ _
          rw [ennreal_ofReal_rpow_of_pos hnorm, ennreal_ofReal_rpow_of_pos hlowpos]
          exact ENNReal.ofReal_le_ofReal hpow
        have hballn : x ∈ Metric.ball 0 (R / (2 : ℝ) ^ n) := by
          simpa [Metric.mem_ball, dist_zero_right] using hhi
        have hcover : coverTerm n x = ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) := by
          simp [coverTerm, hballn]
        calc
          B.indicator density x = density x := by simp [(hx)]
          _ ≤ coverTerm n x := by rw [hcover]; exact hden
          _ ≤ ∑' j : ℕ, coverTerm j x :=
            ENNReal.le_tsum (f := fun j => coverTerm j x) n
    · simp [hx]
  calc
    weightedGmcBallMass γ μ α 0 R = ∫⁻ x, B.indicator density x ∂μ := by
      rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
      simp [B, density]
    _ ≤ ∫⁻ x, ∑' n : ℕ, coverTerm n x ∂μ := lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ x, coverTerm n x ∂μ := by
      rw [lintegral_tsum]
      intro n
      exact (measurable_const.indicator (Metric.isOpen_ball.measurableSet)).aemeasurable
    _ = ∑' n : ℕ,
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
          μ (Metric.ball 0 (R / (2 : ℝ) ^ n)) := by
      congr 1
      funext n
      rw [show coverTerm n = (Metric.ball 0 (R / (2 : ℝ) ^ n)).indicator
        (fun _ => ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) by rfl]
      rw [lintegral_indicator_const (Metric.isOpen_ball.measurableSet)]

/-- Translation of the weighted ball integral to a centered ball for the pushforward measure. -/
theorem weightedGmcBallMass_translate
    (μ : Measure ℂ) (γ α R : ℝ) (z : ℂ) :
    weightedGmcBallMass γ μ α z R =
      weightedGmcBallMass γ (Measure.map (fun x : ℂ => x - z) μ) α 0 R := by
  classical
  let f : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x - (0 : ℂ)‖) (-γ * α)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  rw [weightedGmcBallMass, weightedGmcBallMass,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  change (∫⁻ x, (Metric.ball z R).indicator
      (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - z‖) (-γ * α)) x ∂μ) =
    ∫⁻ x, (Metric.ball 0 R).indicator f x ∂Measure.map (fun x : ℂ => x - z) μ
  rw [lintegral_map' (by
    exact (hf.indicator Metric.isOpen_ball.measurableSet).aemeasurable)
    (measurable_sub_const z).aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Metric.ball z R
  · have hy : x - z ∈ Metric.ball 0 R := by
      simpa [Metric.mem_ball, dist_zero_right, dist_eq_norm] using hx
    simp [hx, hy, f]
  · have hy : x - z ∉ Metric.ball 0 R := by
      intro hy
      apply hx
      simpa [Metric.mem_ball, dist_zero_right, dist_eq_norm] using hy
    simp [hx, hy, f]

/-- Translation of a ball mass under the corresponding pushforward measure. -/
theorem measure_sub_pushforward_ball
    (μ : Measure ℂ) (z : ℂ) (R : ℝ) :
    Measure.map (fun x : ℂ => x - z) μ (Metric.ball 0 R) = μ (Metric.ball z R) := by
  rw [Measure.map_apply (measurable_sub_const z) Metric.isOpen_ball.measurableSet]
  congr 1
  ext x
  simp [Metric.mem_ball, dist_eq_norm]

/-- Dyadic upper bound for a negative-power insertion about an arbitrary center. -/
theorem weightedGmcBallMass_le_dyadic_charge_center
    (μ : Measure ℂ) (γ α R : ℝ) (z : ℂ) (hγ : 0 < γ) (hα : 0 < α)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    weightedGmcBallMass γ μ α z R ≤
      ∑' n : ℕ,
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
          μ (Metric.ball z (R / (2 : ℝ) ^ n)) := by
  have htranslate := weightedGmcBallMass_translate μ γ α R z
  have hroot := weightedGmcBallMass_root_le_dyadic_charge
    (Measure.map (fun x : ℂ => x - z) μ) γ α R hγ hα hR hR1
  rw [htranslate]
  simpa only [measure_sub_pushforward_ball] using hroot

end DOZZ.Proofs
