/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WeakConvGrid

/-! # Double integrals under weak convergence in probability

If finite random measures `μ n` converge weakly in probability to `μ₀` and `μ₀` almost surely has
no atoms, then double integrals of bounded kernels `H n` that converge uniformly away from the
diagonal to a kernel `H₀`, continuous in the first variable away from the diagonal, converge in
probability. The proof compares both sides with finite grid sums, which converge by the single
integral convergence; the error is a modulus-of-continuity term plus the near-diagonal mass,
which is small in probability because `μ₀` has no atoms. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℕ → Ω → Measure ℂ}
  {μ₀ : Ω → Measure ℂ}

namespace BPZWeakConv

theorem measurable_integral (hμ : BPZWeakConv P μ μ₀) {f : ℂ → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω => ∫ x, f x ∂μ n ω) :=
  (measurable_integral_measure hf).comp (hμ.meas n)

end BPZWeakConv

theorem bpz_indicator_one_abs_le (A : Set ℂ) (x : ℂ) : |A.indicator (1 : ℂ → ℝ) x| ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

theorem bpz_indicator_one_eq_zero_of_subset {A : Set ℂ} {R : ℝ}
    (hA : A ⊆ Metric.closedBall 0 R) (x : ℂ) (hx : R < ‖x‖) : A.indicator (1 : ℂ → ℝ) x = 0 :=
  Set.indicator_of_notMem (fun hxA => hx.not_ge (by simpa using hA hxA)) _

theorem bpzGrid_cell_subset (h : ℝ) (hh : 0 < h) (i : ℤ × ℤ) :
    bpzGridIdx h ⁻¹' {i} ⊆ Metric.closedBall 0 (‖bpzGridCorner h i‖ + 2 * h) := by
  intro x hx
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have := norm_sub_bpzGridCorner_le hh x
  rw [hx] at this
  calc ‖x‖ = ‖(x - bpzGridCorner h i) + bpzGridCorner h i‖ := by ring_nf
    _ ≤ ‖x - bpzGridCorner h i‖ + ‖bpzGridCorner h i‖ := norm_add_le _ _
    _ ≤ 2 * h + ‖bpzGridCorner h i‖ := by linarith
    _ = ‖bpzGridCorner h i‖ + 2 * h := by ring

theorem bpz_ball_subset_closedBall (c : ℂ) (r : ℝ) :
    Metric.ball c r ⊆ Metric.closedBall 0 (‖c‖ + |r|) := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖x‖ = ‖(x - c) + c‖ := by ring_nf
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ |r| + ‖c‖ := by linarith [le_abs_self r]
    _ = ‖c‖ + |r| := by ring

namespace BPZWeakConv

/-- Convergence of the mass of any bounded Borel set. -/
theorem conv_mass (hμ : BPZWeakConv P μ μ₀) {s : Set ℂ} (hs : MeasurableSet s)
    {R : ℝ} (hR : s ⊆ Metric.closedBall 0 R) :
    TendstoInMeasure P (fun n ω => (μ n ω).real s) atTop (fun ω => (μ₀ ω).real s) := by
  simpa only [integral_indicator_one hs] using
    hμ.conv (s.indicator 1) (measurable_one.indicator hs) 1 R (bpz_indicator_one_abs_le s)
      (bpz_indicator_one_eq_zero_of_subset hR)

/-- Convergence of grid sums with random coefficients that converge in probability. -/
theorem conv_cellSum [IsFiniteMeasure P] (hμ : BPZWeakConv P μ μ₀)
    {h : ℝ} (hh : 0 < h) (s : Finset (ℤ × ℤ)) (F : ℕ → Ω → ℤ × ℤ → ℝ) (F₀ : Ω → ℤ × ℤ → ℝ)
    (hm : ∀ n i, Measurable (F n · i))
    (hc : ∀ i, TendstoInMeasure P (fun n ω => F n ω i) atTop (F₀ · i)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, (μ n ω).real (bpzGridIdx h ⁻¹' {i}) * F n ω i) atTop
      (fun ω => ∑ i ∈ s, (μ₀ ω).real (bpzGridIdx h ⁻¹' {i}) * F₀ ω i) := by
  have hm' (i : ℤ × ℤ) (n : ℕ) :=
    ((Measure.measurable_coe (measurableSet_bpzGridCell h i)).comp (hμ.meas n)).ennreal_toReal
  exact bpz_tendstoInMeasure_finset_sum s (fun i n => ((hm' i n).mul (hm n i)).aestronglyMeasurable)
    (fun i _ => bpz_tendstoInMeasure_mul (fun n => (hm' i n).aestronglyMeasurable)
      (fun n => (hm n i).aestronglyMeasurable) (hμ.conv_mass (measurableSet_bpzGridCell h i)
        (bpzGrid_cell_subset h hh i)) (hc i))

/-- **Double integrals under weak convergence in probability.** Bounded kernels `H n` supported
in a ball, converging uniformly away from the diagonal to a kernel `H₀` that is uniformly
continuous in the first variable away from the diagonal, have double integrals converging in
probability, provided the limit measure has no atoms. -/
theorem tendstoInMeasure_double [IsProbabilityMeasure P] (hμ : BPZWeakConv P μ μ₀)
    (hatom : ∀ᵐ ω ∂P, ∀ x, μ₀ ω {x} = 0)
    (H : ℕ → ℂ → ℂ → ℝ) (H₀ : ℂ → ℂ → ℝ)
    (hHm : ∀ n, Measurable (Function.uncurry (H n))) (hH₀m : Measurable (Function.uncurry H₀))
    {C R : ℝ} (hR : 0 ≤ R) (hbd : ∀ n x y, |H n x y| ≤ C) (hbd₀ : ∀ x y, |H₀ x y| ≤ C)
    (hsupp : ∀ n x y, (R < ‖x‖ ∨ R < ‖y‖) → H n x y = 0)
    (hsupp₀ : ∀ x y, (R < ‖x‖ ∨ R < ‖y‖) → H₀ x y = 0)
    (hcont : ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x x' y, η ≤ ‖x - y‖ →
      ‖x - x'‖ ≤ δ → |H₀ x y - H₀ x' y| ≤ ε)
    (hunif : ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x y, η ≤ ‖x - y‖ →
      |H n x y - H₀ x y| ≤ ε) :
    TendstoInMeasure P (fun n ω => ∫ x, ∫ y, H n x y ∂μ n ω ∂μ n ω) atTop
      (fun ω => ∫ x, ∫ y, H₀ x y ∂μ₀ ω ∂μ₀ ω) := by
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  let η := fun k => e k / 2
  choose δ hδ hmod using fun k => hcont (η k) (half_pos (he k)) (e k) (he k)
  let h := fun k => min (min (η k / 4) (1 / 4)) (δ k / 2)
  have hh (k : ℕ) : 0 < h k := lt_min (lt_min (by dsimp [η]; positivity) (by norm_num)) (half_pos (hδ k))
  have hh1 (k : ℕ) : h k ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hhη (k : ℕ) : η k + 4 * h k ≤ e k := by
    have hh' : h k ≤ η k / 4 := (min_le_left _ _).trans (min_le_left _ _)
    dsimp only [η] at hh' ⊢
    linarith
  have hhδ (k : ℕ) : 2 * h k ≤ δ k := by
    have : h k ≤ δ k / 2 := min_le_right _ _
    linarith
  let ρ := 2 * R + 1
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  let c := fun k => bpzGridCorner (h k)
  let ball := fun k i => Metric.ball (c k i) (η k + 2 * h k)
  let A := fun k (m : Measure ℂ) => ∑ i ∈ bpzGridBox ⌈R / h k⌉₊,
    m.real (bpzGridIdx (h k) ⁻¹' {i}) * ∫ y, H₀ (c k i) y ∂m
  let G := fun k (m : Measure ℂ) => ∑ i ∈ bpzGridBox ⌈ρ / h k⌉₊,
    m.real (bpzGridIdx (h k) ⁻¹' {i}) * m.real (ball k i)
  let W := fun (m : Measure ℂ) => m.real (Metric.closedBall 0 ρ) * m.real (Metric.closedBall 0 R)
  let B := fun k m => 2 * e k * W m + 2 * C * G k m
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbd₀ 0 0)
  have hm {f : Ω → Measure ℂ} (hf : Measurable f) {s : Set ℂ} (hs : MeasurableSet s) :
      Measurable (fun ω => (f ω).real s) := ((Measure.measurable_coe hs).comp hf).ennreal_toReal
  have hWm {f : Ω → Measure ℂ} (hf : Measurable f) : Measurable (W ∘ f) :=
    (hm hf measurableSet_closedBall).mul (hm hf measurableSet_closedBall)
  have hGm (k : ℕ) {f : Ω → Measure ℂ} (hf : Measurable f) : Measurable (G k ∘ f) :=
    Finset.measurable_sum _ fun i _ => (hm hf (measurableSet_bpzGridCell (h k) i)).mul (hm hf measurableSet_ball)
  have hA (k : ℕ) : TendstoInMeasure P (fun n => A k ∘ μ n) atTop (A k ∘ μ₀) := by
    have hf (i) : Measurable (H₀ (c k i)) := hH₀m.comp (measurable_const.prodMk measurable_id)
    exact hμ.conv_cellSum (hh k) _ (fun n ω i => ∫ y, H₀ (c k i) y ∂μ n ω)
      (fun ω i => ∫ y, H₀ (c k i) y ∂μ₀ ω) (fun n i => hμ.measurable_integral (hf i) n)
      (fun i => hμ.conv _ (hf i) C R (hbd₀ _) fun y hy => hsupp₀ _ y (Or.inr hy))
  have hG (k : ℕ) : TendstoInMeasure P (fun n => G k ∘ μ n) atTop (G k ∘ μ₀) :=
    hμ.conv_cellSum (hh k) _ (fun n ω i => (μ n ω).real (ball k i)) (fun ω i => (μ₀ ω).real (ball k i))
      (fun n i => hm (hμ.meas n) measurableSet_ball)
      (fun i => hμ.conv_mass measurableSet_ball (bpz_ball_subset_closedBall _ _))
  have hW : TendstoInMeasure P (fun n => W ∘ μ n) atTop (W ∘ μ₀) :=
    bpz_tendstoInMeasure_mul (fun n => (hm (hμ.meas n) measurableSet_closedBall).aestronglyMeasurable)
      (fun n => (hm (hμ.meas n) measurableSet_closedBall).aestronglyMeasurable)
      (hμ.conv_mass measurableSet_closedBall (subset_rfl (a := Metric.closedBall 0 ρ)))
      (hμ.conv_mass measurableSet_closedBall (subset_rfl (a := Metric.closedBall 0 R)))
  have hB (k : ℕ) : TendstoInMeasure P (fun n => B k ∘ μ n) atTop (B k ∘ μ₀) :=
    tendstoInMeasure_add P _ _ _ _
      (bpz_tendstoInMeasure_const_mul_of_tendsto tendsto_const_nhds
        (fun n => (hWm (hμ.meas n)).aestronglyMeasurable) hW)
      (bpz_tendstoInMeasure_const_mul_of_tendsto tendsto_const_nhds
        (fun n => (hGm k (hμ.meas n)).aestronglyMeasurable) (hG k))
  refine bpz_tendstoInMeasure_of_dominated_approx hA hB (fun k =>
    (((hWm hμ.meas₀).const_mul (2 * e k)).add ((hGm k hμ.meas₀).const_mul (2 * C))).aestronglyMeasurable) ?_ ?_ ?_
  · filter_upwards [hatom] with ω hω
    let := hμ.fin₀ ω
    have hg0 : Tendsto (fun k => G k (μ₀ ω)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_bpzNearDiag_zero (μ₀ ω) hω (2 * ρ + 1)) (fun _ => Finset.sum_nonneg fun _ _ =>
          mul_nonneg measureReal_nonneg measureReal_nonneg) fun k => ?_
      exact (grid_le_bpzNearDiag (μ₀ ω) (t := η k) (hh k)
        (bpzGrid_box_radius hρ (hh k) (hh1 k))).trans (bpzNearDiag_mono le_rfl (hhη k) _)
    simpa only [B, e, Function.comp_apply, mul_zero, zero_mul, add_zero] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)).mul_const (W (μ₀ ω))).add
        (hg0.const_mul (2 * C))
  · intro k
    filter_upwards [hunif (η k) (half_pos (he k)) (e k) (he k)] with n hn
    exact ae_of_all _ fun ω => by
      let := hμ.fin n ω
      refine (bpz_double_grid_error (μ n ω) (H n) H₀ (hHm n) hH₀m hR (hh k) (hh1 k) (hhδ k)
        (he k).le (hbd n) hbd₀ (hsupp n) hsupp₀ hn (hmod k)).trans ?_
      exact add_le_add_right (mul_le_mul_of_nonneg_left (bpzNearDiag_le_grid (μ n ω) (hh k)) (by positivity)) _
  · intro k
    exact ae_of_all _ fun ω => by
      let := hμ.fin₀ ω
      refine (bpz_double_grid_error (μ₀ ω) H₀ H₀ hH₀m hH₀m hR (hh k) (hh1 k) (hhδ k)
        (he k).le hbd₀ hbd₀ hsupp₀ hsupp₀ (fun _ _ _ => by simpa using (he k).le) (hmod k)).trans ?_
      exact add_le_add_right (mul_le_mul_of_nonneg_left (bpzNearDiag_le_grid (μ₀ ω) (hh k)) (by positivity)) _

end BPZWeakConv

end DOZZ.Proofs
