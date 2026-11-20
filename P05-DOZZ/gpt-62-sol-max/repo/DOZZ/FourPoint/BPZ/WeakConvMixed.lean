/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WeakConvDouble

/-! # Random test functions under weak convergence in probability

If `μ n → μ₀` weakly in probability, then `∫ g_n(ω, x) dμ_n(x) → ∫ g₀(ω, x) dμ₀(x)` in probability
for random test functions supported in a fixed ball, equicontinuous in `x` with a modulus scaled
by a finite random variable `V`, and converging uniformly in the same scale. This handles
integrands that depend on the sample through another random measure, such as
`x ↦ ∫ A(x, y) dν(y)`. The proof compares with grid sums `∑ μ(Q_i) g₀(c_i)`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Pathwise error of the grid approximation of a single integral. -/
theorem bpz_single_grid_error (m : Measure ℂ) [IsFiniteMeasure m] (G G₀ : ℂ → ℝ)
    (hGm : Measurable G) {R δ h ε₁ V : ℝ} (hR : 0 ≤ R) (hh : 0 < h) (hh1 : h ≤ 1 / 4)
    (hhδ : 2 * h ≤ δ) (hε₁ : 0 ≤ ε₁) (hV : 0 ≤ V) (hGb : ∀ x, |G x| ≤ V)
    (hG₀b : ∀ x, |G₀ x| ≤ V)
    (hGs : ∀ x, R < ‖x‖ → G x = 0) (hGG : ∀ x, |G x - G₀ x| ≤ ε₁ * V)
    (hcδ : ∀ x x', ‖x - x'‖ ≤ δ → |G₀ x - G₀ x'| ≤ ε₁ * V) :
    |∫ x, G x ∂m - ∑ i ∈ bpzGridBox ⌈R / h⌉₊,
        m.real (bpzGridIdx h ⁻¹' {i}) * G₀ (bpzGridCorner h i)| ≤
      2 * ε₁ * V * m.real (Metric.closedBall 0 (2 * R + 1)) := by
  set S := bpzGridBox ⌈R / h⌉₊ with hS
  rw [← integral_bpzGrid_step h S (fun i => G₀ (bpzGridCorner h i))]
  set st : ℂ → ℝ := fun x =>
    if bpzGridIdx h x ∈ S then G₀ (bpzGridCorner h (bpzGridIdx h x)) else 0 with hst
  have hstm  := measurable_bpzGrid_step h S (fun i => G₀ (bpzGridCorner h i))
  have hstb : ∀ x, |st x| ≤ V := by
    intro x
    simp only [hst]
    split_ifs
    · exact hG₀b _
    · simpa using hV
  set B₂ : Set ℂ := Metric.closedBall 0 (2 * R + 1)
  have hpt : ∀ x, |G x - st x| ≤ 2 * ε₁ * V * B₂.indicator 1 x := by
    intro x
    by_cases hxS : bpzGridIdx h x ∈ S
    · have hx2  :=
        (norm_le_of_bpzGridIdx_mem_box hh hxS).trans (bpzGrid_box_radius hR hh hh1)
      have hi : B₂.indicator (1 : ℂ → ℝ) x = 1 := Set.indicator_of_mem (by simpa [B₂] using hx2) _
      have hst' : st x = G₀ (bpzGridCorner h (bpzGridIdx h x)) := by
        simpa only [hst] using ite_eq_left hxS
      have hxc  :=
        (norm_sub_bpzGridCorner_le hh x).trans hhδ
      rw [hi, hst', mul_one]
      calc |G x - G₀ (bpzGridCorner h (bpzGridIdx h x))|
          ≤ |G x - G₀ x| + |G₀ x - G₀ (bpzGridCorner h (bpzGridIdx h x))| := abs_sub_le _ _ _
        _ ≤ ε₁ * V + ε₁ * V := add_le_add (hGG x) (hcδ x _ hxc)
        _ = 2 * ε₁ * V := by ring
    · have hx : R < ‖x‖ := by
        by_contra hcon
        push Not at hcon
        exact hxS (bpzGridIdx_mem_box hh hcon)
      have hst' : st x = 0 := by simpa only [hst] using ite_eq_right hxS
      rw [hGs x hx, hst', sub_zero, abs_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hIG : Integrable G m := integrable_of_bdd_finite hGm hGb
  have hIst : Integrable st m := integrable_of_bdd_finite hstm hstb
  rw [← integral_sub hIG hIst, ← Real.norm_eq_abs]
  calc ‖∫ x, (G x - st x) ∂m‖ ≤ ∫ x, 2 * ε₁ * V * B₂.indicator 1 x ∂m := by
        refine norm_integral_le_of_norm_le
          ((((integrable_const (1 : ℝ)).indicator measurableSet_closedBall).const_mul
            (2 * ε₁ * V))) (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact hpt x
    _ = 2 * ε₁ * V * m.real B₂ := by
        rw [integral_const_mul, integral_indicator_one measurableSet_closedBall]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℕ → Ω → Measure ℂ}
  {μ₀ : Ω → Measure ℂ}

namespace BPZWeakConv

/-- Integrals of jointly measurable random integrands against a measurable family of finite
measures are measurable. -/
theorem measurable_integral_random {m : Ω → Measure ℂ} (hm : Measurable m)
    (hmfin : ∀ ω, IsFiniteMeasure (m ω)) {g : Ω → ℂ → ℝ}
    (hg : Measurable (fun p : Ω × ℂ => g p.1 p.2)) :
    Measurable (fun ω => ∫ x, g ω x ∂m ω) :=
  (measurable_integral_finite_family m hm hmfin g hg).comp (measurable_id.prodMk measurable_id)

/-- **Random test functions under weak convergence in probability.** -/
theorem tendstoInMeasure_random_test [IsProbabilityMeasure P] (hμ : BPZWeakConv P μ μ₀)
    (g : ℕ → Ω → ℂ → ℝ) (g₀ : Ω → ℂ → ℝ)
    (hgm : ∀ n, Measurable (fun p : Ω × ℂ => g n p.1 p.2))
    (hg₀m : Measurable (fun p : Ω × ℂ => g₀ p.1 p.2))
    {R : ℝ} (hR : 0 ≤ R) {V : Ω → ℝ} (hVm : Measurable V) (hV0 : ∀ ω, 0 ≤ V ω)
    (hgb : ∀ n, ∀ᵐ ω ∂P, ∀ x, |g n ω x| ≤ V ω) (hg₀b : ∀ᵐ ω ∂P, ∀ x, |g₀ ω x| ≤ V ω)
    (hsupp : ∀ n ω x, R < ‖x‖ → g n ω x = 0) (hsupp₀ : ∀ ω x, R < ‖x‖ → g₀ ω x = 0)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ ω ∂P, ∀ x x', ‖x - x'‖ ≤ δ →
      |g₀ ω x - g₀ ω x'| ≤ ε * V ω)
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ x, |g n ω x - g₀ ω x| ≤ ε * V ω) :
    TendstoInMeasure P (fun n ω => ∫ x, g n ω x ∂μ n ω) atTop
      (fun ω => ∫ x, g₀ ω x ∂μ₀ ω) := by
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  choose δ hδ hmod using fun k => hcont (e k) (he k)
  let h := fun k => min (1 / 4) (δ k / 2)
  have hh (k : ℕ) : 0 < h k := lt_min (by norm_num) (half_pos (hδ k))
  have hh1 (k : ℕ) : h k ≤ 1 / 4 := min_le_left _ _
  have hhδ (k : ℕ) : 2 * h k ≤ δ k := by
    have : h k ≤ δ k / 2 := min_le_right _ _
    linarith
  let A := fun k (m : Ω → Measure ℂ) ω => ∑ i ∈ bpzGridBox ⌈R / h k⌉₊,
    (m ω).real (bpzGridIdx (h k) ⁻¹' {i}) * g₀ ω (bpzGridCorner (h k) i)
  let S := Metric.closedBall (0 : ℂ) (2 * R + 1)
  let B := fun k (m : Ω → Measure ℂ) ω => (2 * e k * V ω) * (m ω).real S
  have hA (k : ℕ) : TendstoInMeasure P (fun n => A k (μ n)) atTop (A k μ₀) := by
    have hm (i) := hg₀m.comp (measurable_id.prodMk (measurable_const (a := bpzGridCorner (h k) i)))
    exact hμ.conv_cellSum (hh k) _ _ _ (fun _ i => hm i) (fun i =>
      tendstoInMeasure_of_tendsto_ae (fun _ => (hm i).aestronglyMeasurable) (ae_of_all _ fun _ => tendsto_const_nhds))
  have hmass {m : Ω → Measure ℂ} (hm : Measurable m) : Measurable (fun ω => (m ω).real S) :=
    ((Measure.measurable_coe measurableSet_closedBall).comp hm).ennreal_toReal
  have hB (k : ℕ) : TendstoInMeasure P (fun n => B k (μ n)) atTop (B k μ₀) :=
    bpz_tendstoInMeasure_mul (fun _ => (hVm.const_mul (2 * e k)).aestronglyMeasurable)
      (fun n => (hmass (hμ.meas n)).aestronglyMeasurable)
      (tendstoInMeasure_of_tendsto_ae (fun _ => (hVm.const_mul (2 * e k)).aestronglyMeasurable)
        (ae_of_all _ fun _ => tendsto_const_nhds)) (hμ.conv_mass measurableSet_closedBall (subset_rfl (a := S)))
  refine bpz_tendstoInMeasure_of_dominated_approx hA hB (fun k =>
    ((hVm.const_mul (2 * e k)).mul (hmass hμ.meas₀)).aestronglyMeasurable) (ae_of_all _ fun ω => ?_) ?_ ?_
  · simpa only [B, e, zero_mul, mul_zero] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const (V ω)).mul_const ((μ₀ ω).real S)
  · intro k
    filter_upwards [hunif (e k) (he k)] with n hn
    filter_upwards [hgb n, hg₀b, hn, hmod k] with ω hb hb₀ hu hm
    let := hμ.fin n ω
    exact bpz_single_grid_error (μ n ω) (g n ω) (g₀ ω) ((hgm n).comp (measurable_const.prodMk measurable_id))
      hR (hh k) (hh1 k) (hhδ k) (he k).le (hV0 ω) hb hb₀ (hsupp n ω) hu hm
  · intro k
    filter_upwards [hg₀b, hmod k] with ω hb₀ hm
    let := hμ.fin₀ ω
    exact bpz_single_grid_error (μ₀ ω) (g₀ ω) (g₀ ω) (hg₀m.comp (measurable_const.prodMk measurable_id))
      hR (hh k) (hh1 k) (hhδ k) (he k).le (hV0 ω) hb₀ hb₀ (hsupp₀ ω)
      (fun _ => by simpa using mul_nonneg (he k).le (hV0 ω)) hm

end BPZWeakConv

end DOZZ.Proofs
