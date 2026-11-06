/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.IntegerTranslationClassPacking
import CCDN.ClassGroup.NumberFieldEuclideanLattice

/-! A packing estimate using the separation of distinct algebraic integers.
It is uniform in the number field, including fields of degree one, and
does not require a lower bound on the radius in terms of the discriminant. -/

namespace CCDN
section
open NumberField MeasureTheory MeasureTheory.Measure

theorem separated_finite_ball_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Finset E) {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (2 * R + 1) ^ Module.finrank ℝ E := by
  have hd : Set.PairwiseDisjoint (s : Set E) (fun x ↦ Metric.ball x (1 / 2 : ℝ)) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have hzx' : dist x z < 1 / 2 := by
      simpa [dist_comm] using Metric.mem_ball.mp hzx
    have hzy' := Metric.mem_ball.mp hzy
    have ht := dist_triangle x z y
    have hh := hsep x hx y hy hxy
    rw [← dist_eq_norm] at hh
    linarith
  have hsub : (⋃ x ∈ s, Metric.ball x (1 / 2 : ℝ)) ⊆
      Metric.ball (0 : E) (R + 1 / 2) := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    have hz' : ‖z - x‖ < 1 / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp hzx
    have hx' := hs x hx
    have hh := norm_le_norm_sub_add z x
    exact mem_ball_zero_iff.mpr (by linarith)
  have hm : s.card * μ (Metric.ball (0 : E) (1 / 2 : ℝ)) ≤
      μ (Metric.ball (0 : E) (R + 1 / 2)) := by
    have hu := measure_biUnion_finset (μ := μ) hd (fun _ _ ↦ measurableSet_ball)
    have hmono : μ (⋃ x ∈ s, Metric.ball x (1 / 2 : ℝ)) ≤
        μ (Metric.ball (0 : E) (R + 1 / 2)) := measure_mono hsub
    rw [hu] at hmono
    simpa [addHaar_ball_center μ, Finset.sum_const, nsmul_eq_mul] using hmono
  have ht := ENNReal.toReal_mono measure_ball_lt_top.ne hm
  rw [addHaar_ball_of_pos μ (0 : E) (by norm_num : (0 : ℝ) < 1 / 2),
    addHaar_ball_of_pos μ (0 : E) (by linarith : 0 < R + 1 / 2)] at ht
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 2) ^ Module.finrank ℝ E),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (R + 1 / 2) ^ Module.finrank ℝ E)]
    at ht
  have hv :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 zero_lt_one))
      (measure_ball_lt_top.ne)
  have hpow : s.card * (1 / 2) ^ Module.finrank ℝ E ≤
      (R + 1 / 2) ^ Module.finrank ℝ E := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hpow
    (by positivity : (0 : ℝ) ≤ 2 ^ Module.finrank ℝ E)
  have hhalf : (1 / 2 : ℝ) ^ Module.finrank ℝ E * 2 ^ Module.finrank ℝ E = 1 := by simp_all
  have hradius : (R + 1 / 2) ^ Module.finrank ℝ E * 2 ^ Module.finrank ℝ E =
      (2 * R + 1) ^ Module.finrank ℝ E := by
    rw [← mul_pow]
    congr 1
    ring
  simpa only [mul_assoc, hhalf, mul_one, hradius] using hscale

/-- For `B ≥ 0`, the number of algebraic integers of `K` bounded by `B` at every infinite place
is at most `(2 * √n * B + 1) ^ n`, where `n = [K : ℚ]`. -/
theorem boundedArchimedeanIntegers_separated_count
    (K : Type*) [Field K] [NumberField K] {B : ℝ} (hB : 0 ≤ B) :
    ((boundedArchimedeanIntegers K B).ncard : ℝ) ≤
      (2 * Real.sqrt (Module.finrank ℚ K) * B + 1) ^ Module.finrank ℚ K := by
  classical
  let e : 𝓞 K → mixedEmbedding.euclidean.mixedSpace K :=
    fun x ↦ euclideanNumberFieldEmbedding K (x : K)
  have he : Function.Injective e := by
    intro x y h
    exact RingOfIntegers.coe_injective (euclideanNumberFieldEmbedding_injective K h)
  let s := (boundedArchimedeanIntegers_finite K B).toFinset.image e
  have hs : ∀ x ∈ s, ‖x‖ ≤ Real.sqrt (Module.finrank ℚ K) * B := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact euclideanNumberFieldEmbedding_norm_le K hB z
      ((boundedArchimedeanIntegers_finite K B).mem_toFinset.mp hz)
  have hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    have hzw := sub_ne_zero.mpr (fun h ↦ hxy (congrArg e h))
    have hh := one_le_euclidean_norm_integer K hzw
    grind
  have hcard : s.card = (boundedArchimedeanIntegers K B).ncard := by
    rw [Finset.card_image_of_injective _ he]
    exact Set.ncard_eq_toFinset_card _ (boundedArchimedeanIntegers_finite K B) |>.symm
  have hh := separated_finite_ball_count volume s
    (mul_nonneg (Real.sqrt_nonneg _) hB) hs hsep
  simpa [hcard, mixedEmbedding.euclidean.finrank, mul_assoc] using hh

