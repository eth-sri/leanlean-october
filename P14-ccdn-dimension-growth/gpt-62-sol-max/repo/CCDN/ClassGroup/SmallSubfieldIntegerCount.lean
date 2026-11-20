/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.IntegerTranslationClassPacking
import CCDN.ClassGroup.SubfieldBoundedIntegers
import CCDN.ForMathlib.FieldTheory
import Mathlib.Data.Set.Card.Arithmetic

/-! Parameters lying in intermediate fields of degree at most one
quarter of the ambient degree have a uniform fourth-root contribution
at the balanced discriminant radius. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField

private lemma small_dimension_packing_bound {m n : ℕ} (hm : 4 * m ≤ n)
    {B : ℝ} (hB : 1 ≤ B) :
    (2 * Real.sqrt (m : ℝ) * B + 1) ^ m ≤
      (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) := by
  have hmn : m ≤ n := by omega
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hsq : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (Nat.cast_le.mpr hmn)
  have hc : 1 ≤ 2 * Real.sqrt (n : ℝ) + 1 := by
    simp
  have hbase : 2 * Real.sqrt (m : ℝ) * B + 1 ≤
      (2 * Real.sqrt (n : ℝ) + 1) * B := by nlinarith
  have hexp : (m : ℝ) ≤ (n : ℝ) / 4 := by
    have hh : 4 * (m : ℝ) ≤ n := by exact_mod_cast hm
    linarith
  calc
    _ ≤ ((2 * Real.sqrt (n : ℝ) + 1) * B) ^ m :=
      pow_le_pow_left₀ (by positivity) hbase m
    _ = (2 * Real.sqrt (n : ℝ) + 1) ^ m * B ^ m := mul_pow _ _ _
    _ ≤ (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4) := by
      apply mul_le_mul (pow_le_pow_right₀ hc hmn) _ (by positivity) (by positivity)
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hB hexp

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic integers of `K` bounded by `B` at every infinite place that lie in an intermediate
field `L` with `4 * [L : ℚ] ≤ [K : ℚ]`. -/
def boundedSmallSubfieldIntegers (B : ℝ) : Set (𝓞 K) :=
  {β | β ∈ boundedArchimedeanIntegers K B ∧
    ∃ L : IntermediateField ℚ K,
      4 * Module.finrank ℚ L ≤ Module.finrank ℚ K ∧ (β : K) ∈ L}

/-- The set `boundedSmallSubfieldIntegers K B` is finite. -/
lemma boundedSmallSubfieldIntegers_finite (B : ℝ) :
    (boundedSmallSubfieldIntegers K B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset (fun _ h ↦ h.1)

/-- The constant `2 ^ n * (2 * √n + 1) ^ n` in the count of bounded integers in small subfields of
a number field of degree `n`. -/
def smallSubfieldIntegerCountConstant (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (2 * Real.sqrt (n : ℝ) + 1) ^ n

/-- The constant `smallSubfieldIntegerCountConstant n` is positive. -/
lemma smallSubfieldIntegerCountConstant_pos (n : ℕ) :
    0 < smallSubfieldIntegerCountConstant n := by
  unfold smallSubfieldIntegerCountConstant
  positivity

private theorem boundedSmallSubfieldIntegers_count {B : ℝ} (hB : 1 ≤ B) :
    ((boundedSmallSubfieldIntegers K B).ncard : ℝ) ≤
      smallSubfieldIntegerCountConstant (Module.finrank ℚ K) *
        B ^ ((Module.finrank ℚ K : ℝ) / 4) := by
  classical
  let n := Module.finrank ℚ K
  let T := {L : IntermediateField ℚ K // 4 * Module.finrank ℚ L ≤ n}
  let : Finite (IntermediateField ℚ K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ K
      (Field.exists_primitive_element ℚ K)
  let : Fintype T := Fintype.ofFinite T
  let f (L : T) := boundedIntegersInSubfield K L.val B
  let C := (2 * Real.sqrt (n : ℝ) + 1) ^ n * B ^ ((n : ℝ) / 4)
  have he : boundedSmallSubfieldIntegers K B = ⋃ L, f L := by
    ext β
    simp only [boundedSmallSubfieldIntegers, boundedIntegersInSubfield, f, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    aesop
  have hcard : (Fintype.card T : ℝ) ≤ (2 : ℝ) ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast (Nat.card_le_card_of_injective (f := (Subtype.val : T → _))
      Subtype.val_injective).trans (IntermediateField.card_le_two_pow_finrank ℚ K)
  calc
    _ ≤ ∑ L, ((f L).ncard : ℝ) := by
      rw [he]
      exact_mod_cast Set.ncard_iUnion_le_of_fintype f
    _ ≤ ∑ _L : T, C := Finset.sum_le_sum fun L _ =>
      (boundedIntegersInSubfield_count K L.val (by linarith)).trans (small_dimension_packing_bound L.property hB)
    _ = Fintype.card T * C := by simp
    _ ≤ (2 : ℝ) ^ n * C := by gcongr
    _ = _ := by simp [n, C, smallSubfieldIntegerCountConstant, mul_assoc]

/-- At the balanced radius `9 * D ^ (1 / n)` with `D ≥ 1` and `n = [K : ℚ]`, the number of bounded
integers in small subfields is at most a constant depending only on `n` times `D ^ (1 / 4)`. -/
theorem boundedSmallSubfieldIntegers_balanced_count {D : ℝ} (hD : 1 ≤ D) :
    ((boundedSmallSubfieldIntegers K
        (9 * D ^ (1 / (Module.finrank ℚ K : ℝ)))).ncard : ℝ) ≤
      (smallSubfieldIntegerCountConstant (Module.finrank ℚ K) *
        (9 : ℝ) ^ ((Module.finrank ℚ K : ℝ) / 4)) * D ^ (1 / 4 : ℝ) := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hD0 := zero_lt_one.trans_le hD
  have hB : 1 ≤ 9 * D ^ (1 / (Module.finrank ℚ K : ℝ)) := by
    have hh := Real.one_le_rpow hD (by positivity : 0 ≤ 1 / (Module.finrank ℚ K : ℝ))
    linarith
  have hh := boundedSmallSubfieldIntegers_count K hB
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9) (Real.rpow_nonneg hD0.le _),
    ← Real.rpow_mul hD0.le] at hh
  grind

end
end CCDN
