/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.IntegerTranslationClassPacking
public import CCDN.ClassGroup.NumberFieldEuclideanLattice

/-! A packing estimate using the separation of distinct algebraic integers.
It is uniform in the number field, including fields of degree one, and
does not require a lower bound on the radius in terms of the discriminant. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField MeasureTheory MeasureTheory.Measure

private theorem separated_finite_ball_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (s : Finset E) {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (2 * R + 1) ^ Module.finrank ℝ E := by
  let δ : ℝ := 1 / 2
  have hδ : 0 < δ := by norm_num [δ]
  have hd : Set.PairwiseDisjoint (s : Set E) (fun x ↦ Metric.ball x δ) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by simpa [δ, dist_eq_norm, ← two_mul] using hsep x hx y hy hxy)
  have hsub : (⋃ x ∈ s, Metric.ball x δ) ⊆ Metric.ball (0 : E) (R + δ) :=
    Set.iUnion₂_subset fun x hx => Metric.ball_subset_ball' (by simpa [add_comm] using hs x hx)
  have hm := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hd (fun _ _ ↦ measurableSet_ball),
    addHaar_ball_of_pos _ _ (add_pos_of_nonneg_of_pos hR hδ)] at hm
  simp_rw [addHaar_ball_of_pos μ _ hδ] at hm
  simp only [Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at hm
  have hh := (ENNReal.mul_le_mul_iff_left
    (Metric.measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne).mp hm
  have ht := ENNReal.toReal_le_of_le_ofReal (by positivity) hh
  rw [show 2 * R + 1 = (R + δ) / δ by dsimp [δ]; ring, div_pow, le_div_iff₀ (by positivity)]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using ht

open Classical in
/-- Embed the bounded algebraic integers into the Euclidean integer lattice. -/
theorem exists_bounded_integer_lattice_finset (K : Type*) [Field K] [NumberField K]
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ s : Finset (mixedEmbedding.euclidean.integerLattice K),
      s.card = (boundedArchimedeanIntegers K B).ncard ∧
      ∀ x ∈ s, ‖(x : mixedEmbedding.euclidean.mixedSpace K)‖ ≤
        Real.sqrt (Module.finrank ℚ K) * B := by
  let e : 𝓞 K ↪ mixedEmbedding.euclidean.integerLattice K :=
    ⟨fun x => ⟨euclideanNumberFieldEmbedding K (x : K),
      euclideanNumberFieldEmbedding_mem_integerLattice K x⟩,
      fun _ _ h => RingOfIntegers.coe_injective
        (euclideanNumberFieldEmbedding_injective K (congrArg Subtype.val h))⟩
  refine ⟨(boundedArchimedeanIntegers_finite K B).toFinset.map e,
    by simp [← Set.ncard_eq_toFinset_card], ?_⟩
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
  exact euclideanNumberFieldEmbedding_norm_le K hB (z : K) ((boundedArchimedeanIntegers_finite K B).mem_toFinset.mp hz)

/-- For `B ≥ 0`, the number of algebraic integers of `K` bounded by `B` at every infinite place
is at most `(2 * √n * B + 1) ^ n`, where `n = [K : ℚ]`. -/
theorem boundedArchimedeanIntegers_separated_count
    (K : Type*) [Field K] [NumberField K] {B : ℝ} (hB : 0 ≤ B) :
    ((boundedArchimedeanIntegers K B).ncard : ℝ) ≤
      (2 * Real.sqrt (Module.finrank ℚ K) * B + 1) ^ Module.finrank ℚ K := by
  classical
  obtain ⟨s, hc, hs⟩ := exists_bounded_integer_lattice_finset K hB
  let e : mixedEmbedding.euclidean.integerLattice K ↪ mixedEmbedding.euclidean.mixedSpace K :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsep : ∀ x ∈ s.map e, ∀ y ∈ s.map e, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨z, hz⟩ := (mem_euclidean_integerLattice_iff K _).mp
      (Submodule.sub_mem _ a.property b.property)
    rw [← show euclideanNumberFieldEmbedding K (z : K) = e a - e b from hz]
    apply one_le_euclidean_norm_integer
    rintro rfl
    apply hxy
    simpa [e, sub_eq_zero] using hz.symm
  have h := separated_finite_ball_count volume (s.map e) (mul_nonneg (Real.sqrt_nonneg _) hB)
    (by simpa [e] using hs) hsep
  simpa [hc, mixedEmbedding.euclidean.finrank, mul_assoc] using h

end
end CCDN
