/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.IntegerTranslationClassPacking
import CCDN.ClassGroup.LatticeFinitePacking
import CCDN.ClassGroup.SeparatedIntegerPacking

/-! Finite-radius counting for the algebraic integers. The input
is a short independent integral basis over the reals; it is not required
to generate the ring of integers over `ℤ`. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory

private theorem unitBall_volume_eq_euclidean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    volume.real (Metric.ball (0 : E) 1) =
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) 1) := by
  let b := stdOrthonormalBasis ℝ E
  unfold Measure.real
  rw [← b.measurePreserving_repr_symm.measure_preimage measurableSet_ball.nullMeasurableSet]
  simp [LinearIsometryEquiv.preimage_ball]

variable (K : Type*) [Field K] [NumberField K]

/-- A dimension-only coefficient for the box count when the independent
integral vectors have norm at most `C` times the box radius. -/
def numberFieldLatticeBoxConstant (n : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ n * (Real.sqrt n + n * C) ^ n *
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The box-count constant `numberFieldLatticeBoxConstant n C` is nonnegative for `C ≥ 0`. -/
lemma numberFieldLatticeBoxConstant_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ numberFieldLatticeBoxConstant n C := by
  unfold numberFieldLatticeBoxConstant
  positivity

open Classical in
private theorem boundedArchimedeanIntegers_count_of_relative_short_basis
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hnorm : ∀ i, ‖b i‖ ≤ C * B) :
    ((boundedArchimedeanIntegers K B).ncard : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      numberFieldLatticeBoxConstant (Module.finrank ℚ K) C * B ^ Module.finrank ℚ K := by
  obtain ⟨s, hcard, hs⟩ := exists_bounded_integer_lattice_finset K hB
  have hp := superlattice_finite_packing_polynomial b
    (mixedEmbedding.euclidean.integerLattice K) hb s (by positivity) (by positivity) hs hnorm
  rw [hcard, euclidean_integerLattice_covolume, unitBall_volume_eq_euclidean,
    ← Module.finrank_eq_card_basis b, mixedEmbedding.euclidean.finrank] at hp
  have hr : nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have := card_add_two_mul_card_eq_rank K
    omega
  have hpow : (2 : ℝ)⁻¹ ^ Module.finrank ℚ K ≤ (2 : ℝ)⁻¹ ^ nrComplexPlaces K :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
  have hc := mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg |(discr K : ℝ)|)
  have hs := (mul_le_mul_of_nonneg_left hc
    (Nat.cast_nonneg (boundedArchimedeanIntegers K B).ncard)).trans hp
  have he :
      ((boundedArchimedeanIntegers K B).ncard : ℝ) *
          ((2 : ℝ)⁻¹ ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)|) =
        (((boundedArchimedeanIntegers K B).ncard : ℝ) * Real.sqrt |(discr K : ℝ)|) /
          (2 : ℝ) ^ Module.finrank ℚ K := by
    rw [inv_pow, div_eq_mul_inv]
    ring
  rw [he] at hs
  have ht := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mp hs
  have hrad : Real.sqrt (Module.finrank ℚ K) * B +
      (Module.finrank ℚ K : ℝ) * (C * B) =
      (Real.sqrt (Module.finrank ℚ K) + Module.finrank ℚ K * C) * B := by ring
  rw [hrad, mul_pow] at ht
  exact ht.trans_eq (by unfold numberFieldLatticeBoxConstant; ring)

open Classical in
/-- Dividing by short integer translates gives the expected
one-dimensional saving for translation classes. -/
theorem boundedSquareNormTranslationClasses_count_of_relative_short_basis
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (mixedEmbedding.euclidean.mixedSpace K))
    (hb : ∀ i, b i ∈ mixedEmbedding.euclidean.integerLattice K)
    {B C : ℝ} (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hnorm : ∀ i, ‖b i‖ ≤ C * B) :
    ((boundedSquareNormTranslationClasses K B).card : ℝ) *
        Real.sqrt |(discr K : ℝ)| ≤
      (numberFieldLatticeBoxConstant (Module.finrank ℚ K) C *
        (2 : ℝ) ^ Module.finrank ℚ K) * B ^ (Module.finrank ℚ K - 1) := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hp := boundedSquareNormTranslationClasses_packing K B B
  have hpR :
      ((boundedSquareNormTranslationClasses K B).card : ℝ) *
          ((integerInterval B).card : ℝ) ≤
        (boundedArchimedeanIntegers K (2 * B)).ncard := by
    exact_mod_cast (by simpa [two_mul] using hp)
  have htranslates : B ≤ ((integerInterval B).card : ℝ) := by
    rw [integerInterval_card_cast hBpos.le]
    linarith [Int.lt_floor_add_one B]
  have hcard := (mul_le_mul_of_nonneg_left htranslates
    (Nat.cast_nonneg (boundedSquareNormTranslationClasses K B).card)).trans hpR
  have hcount := boundedArchimedeanIntegers_count_of_relative_short_basis K b hb
    (B := 2 * B) (by positivity) hC (fun i ↦ (hnorm i).trans (by
      nlinarith))
  have hh := (mul_le_mul_of_nonneg_right hcard
    (Real.sqrt_nonneg |(discr K : ℝ)|)).trans hcount
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hpow : B ^ Module.finrank ℚ K = B ^ (Module.finrank ℚ K - 1) * B := by
    rw [← pow_succ]
    congr 1
    omega
  rw [mul_pow, hpow] at hh
  apply (mul_le_mul_iff_left₀ hBpos).mp
  linarith

end
end CCDN
