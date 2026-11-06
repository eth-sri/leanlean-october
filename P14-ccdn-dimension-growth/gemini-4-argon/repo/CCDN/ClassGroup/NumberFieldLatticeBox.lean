/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.IntegerTranslationClassPacking
import CCDN.ClassGroup.LatticeFinitePacking
import CCDN.ClassGroup.NumberFieldEuclideanLattice

/-! Finite-radius counting for the algebraic integers. The input
is a short independent integral basis over the reals; it is not required
to generate the ring of integers over `ℤ`. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory

variable (K : Type*) [Field K] [NumberField K]

/-- A dimension-only coefficient for the box count when the independent
integral vectors have norm at most `C` times the box radius. -/
def numberFieldLatticeBoxConstant (n : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ n * (2 : ℝ) ^ n * (2 * Real.sqrt n + n * C) ^ n

/-- The box-count constant `numberFieldLatticeBoxConstant n C` is nonnegative for `C ≥ 0`. -/
lemma numberFieldLatticeBoxConstant_nonneg (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ numberFieldLatticeBoxConstant n C := by
  unfold numberFieldLatticeBoxConstant; positivity

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
  let R := 2 * B
  let M := C * R
  have hR0 : 0 ≤ R := by positivity
  have hM0 : 0 ≤ M := mul_nonneg hC hR0
  let E := mixedEmbedding.euclidean.mixedSpace K
  let L := mixedEmbedding.euclidean.integerLattice K
  let e : 𝓞 K → L := fun x ↦ ⟨euclideanNumberFieldEmbedding K (x : K),
    euclideanNumberFieldEmbedding_mem_integerLattice K x⟩
  have he : Function.Injective e := fun x y h ↦ RingOfIntegers.coe_injective
    (euclideanNumberFieldEmbedding_injective K (congrArg Subtype.val h))
  let s := (boundedArchimedeanIntegers_finite K R).toFinset.image e
  have hs : ∀ x ∈ s, ‖(x : E)‖ ≤ Real.sqrt (Module.finrank ℚ K) * R := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact euclideanNumberFieldEmbedding_norm_le K hR0 (z : K)
      ((boundedArchimedeanIntegers_finite K R).mem_toFinset.mp hz)
  have hp := superlattice_finite_packing_polynomial b L hb s
    (mul_nonneg (Real.sqrt_nonneg _) hR0) hM0 hs fun i ↦ (hnorm i).trans (by dsimp [M, R]; nlinarith)
  rw [Finset.card_image_of_injective _ he,
    ← Set.ncard_eq_toFinset_card _ (boundedArchimedeanIntegers_finite K R),
    euclidean_integerLattice_covolume, mixedEmbedding.euclidean.finrank,
    show Fintype.card ι = Module.finrank ℚ K by
      rw [← Module.finrank_eq_card_basis b, mixedEmbedding.euclidean.finrank]] at hp
  have hunit : volume.real (Metric.ball (0 : E) 1) ≤ (2 : ℝ) ^ Module.finrank ℚ K := by
    let c := stdOrthonormalBasis ℝ E
    let f_e : E → (Fin (Module.finrank ℝ E) → ℝ) :=
      fun x ↦ (MeasurableEquiv.toLp 2 _).symm (c.repr x)
    have hm : MeasurePreserving f_e :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).comp c.measurePreserving_repr
    let U : Set (Fin (Module.finrank ℝ E) → ℝ) := Set.Icc (fun _ ↦ -1) (fun _ ↦ 1)
    have hvol : volume (f_e ⁻¹' U) = (2 : ENNReal) ^ Module.finrank ℝ E := by
      rw [hm.measure_preimage (show MeasurableSet U from measurableSet_Icc).nullMeasurableSet]
      norm_num [U, Real.volume_Icc_pi]
    have hsub : Metric.ball (0 : E) 1 ⊆ f_e ⁻¹' U := fun x hx ↦ by
      have hnorm1 : ‖x‖ < 1 := by simpa using hx
      have hcoord (i : Fin (Module.finrank ℝ E)) : |f_e x i| ≤ 1 := by
        have hi := PiLp.norm_apply_le (c.repr x) i
        rw [c.repr.norm_map] at hi
        exact hi.trans hnorm1.le
      exact ⟨fun i ↦ (abs_le.mp (hcoord i)).1, fun i ↦ (abs_le.mp (hcoord i)).2⟩
    have ht := ENNReal.toReal_mono (by rw [hvol]; finiteness) (measure_mono hsub)
    rw [hvol] at ht
    dsimp only [E] at ht
    simpa only [Measure.real, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      mixedEmbedding.euclidean.finrank] using ht
  have hp1 : ((boundedArchimedeanIntegers K R).ncard : ℝ) *
      ((2 : ℝ)⁻¹ ^ nrComplexPlaces K * Real.sqrt |(discr K : ℝ)|) ≤
      (2 : ℝ) ^ Module.finrank ℚ K *
        (2 * (Real.sqrt (Module.finrank ℚ K) * R) + (Module.finrank ℚ K : ℝ) * M) ^
          Module.finrank ℚ K :=
    hp.trans ((mul_le_mul_of_nonneg_left hunit (by positivity)).trans_eq (by ring))
  have hr : nrComplexPlaces K ≤ Module.finrank ℚ K := by
    have := card_add_two_mul_card_eq_rank K; omega
  have hs_le := (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hr)
      (Real.sqrt_nonneg |(discr K : ℝ)|))
    (Nat.cast_nonneg (boundedArchimedeanIntegers K R).ncard)).trans hp1
  rw [show ((boundedArchimedeanIntegers K R).ncard : ℝ) *
        ((2 : ℝ)⁻¹ ^ Module.finrank ℚ K * Real.sqrt |(discr K : ℝ)|) =
      (((boundedArchimedeanIntegers K R).ncard : ℝ) * Real.sqrt |(discr K : ℝ)|) /
        (2 : ℝ) ^ Module.finrank ℚ K by rw [inv_pow, div_eq_mul_inv]; ring] at hs_le
  have ht := (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mp hs_le
  rw [show 2 * (Real.sqrt (Module.finrank ℚ K) * R) + (Module.finrank ℚ K : ℝ) * M =
      (2 * Real.sqrt (Module.finrank ℚ K) + Module.finrank ℚ K * C) * R by dsimp [M]; ring,
    mul_pow] at ht
  have hcount : ((boundedArchimedeanIntegers K R).ncard : ℝ) * Real.sqrt |(discr K : ℝ)| ≤
      numberFieldLatticeBoxConstant (Module.finrank ℚ K) C * R ^ Module.finrank ℚ K :=
    ht.trans_eq (by unfold numberFieldLatticeBoxConstant; ring)
  have hpR : ((boundedSquareNormTranslationClasses K B).card : ℝ) * ((2 * ⌊B⌋ + 1).toNat : ℝ) ≤
      (boundedArchimedeanIntegers K R).ncard :=
    mod_cast (by simpa only [R, two_mul] using boundedSquareNormTranslationClasses_packing K B B)
  have htranslates : B ≤ ((2 * ⌊B⌋ + 1).toNat : ℝ) := by
    have hfloor : (0 : ℤ) ≤ 2 * ⌊B⌋ + 1 := by
      have : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.mpr hBpos.le; omega
    rw [show ((2 * ⌊B⌋ + 1).toNat : ℝ) = ((2 * ⌊B⌋ + 1 : ℤ) : ℝ) from
      mod_cast Int.toNat_of_nonneg hfloor]
    push_cast; linarith [Int.lt_floor_add_one B]
  have hh := (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left htranslates (Nat.cast_nonneg _)).trans hpR)
    (Real.sqrt_nonneg |(discr K : ℝ)|)).trans hcount
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  dsimp only [R] at hh
  rw [mul_pow, show B ^ Module.finrank ℚ K = B ^ (Module.finrank ℚ K - 1) * B by
    rw [← pow_succ]; congr 1; omega] at hh
  exact (mul_le_mul_iff_left₀ hBpos).mp (by nlinarith only [hh])

end
end CCDN
