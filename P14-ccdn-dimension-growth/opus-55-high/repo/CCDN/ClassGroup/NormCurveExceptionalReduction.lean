/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.SmallSubfieldIntegerCount

/-! The square-norm integers are covered by their integer-translation
fibers. Fibers with even generated-subfield index are absorbed into the
small-subfield set when there is no index-two intermediate field. -/

namespace CCDN
section
open NumberField NumberField.InfinitePlace IntermediateField
open scoped IntermediateField

variable (K : Type*) [Field K] [NumberField K]

variable (hnoTwo : ∀ L : IntermediateField ℚ K, Module.finrank L K ≠ 2)
include hnoTwo

lemma even_index_translate_mem_smallSubfield
    (β : 𝓞 K) (hindex : ¬ Odd (Module.finrank ℚ⟮(β : K)⟯ K))
    {B : ℝ} {α : 𝓞 K} (hα : α ∈ squareNormTranslateFiber K β B) :
    α ∈ boundedSmallSubfieldIntegers K B := by
  let L := ℚ⟮(β : K)⟯
  have he : Even (Module.finrank L K) := by aesop
  have hpos : 0 < Module.finrank L K := Module.finrank_pos
  have hne := hnoTwo L
  have hfour : 4 ≤ Module.finrank L K := by grind
  refine ⟨hα.1.2.1, L, (by
    have ht := Module.finrank_mul_finrank ℚ L K
    nlinarith), ?_⟩
  obtain ⟨x, hx⟩ := hα.2
  rw [hx]
  exact L.sub_mem (L.intCast_mem x) (IntermediateField.mem_adjoin_simple_self ℚ (β : K))

/-- For a number field `K` without an intermediate field of index two, there is an injective family
of algebraic integers `β q` bounded by `B`, indexed by the bounded square-norm translation
classes, such that the number of bounded square-norm integers is at most the number of bounded
integers in small subfields plus the number of points of height at most
`max (2 * B) (√(B ^ n))` on the signed norm curves for those `β q` with `[K : ℚ(β q)]` odd. -/
theorem exists_norm_curve_exception_split
    (B : ℝ) :
    ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
      (boundedSquareNormIntegers K B).ncard ≤
        (boundedSmallSubfieldIntegers K B).ncard +
        ∑ q : boundedSquareNormTranslationClasses K B,
          if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
            count (signedNormCurveLocus K (β q) 1)
              (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) +
            count (signedNormCurveLocus K (β q) (-1))
              (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K)))
          else 0 := by
  classical
  obtain ⟨β, hb, hcover⟩ := exists_norm_translate_cover K B
  refine ⟨β, ?_⟩
  let Q := boundedSquareNormTranslationClasses K B
  let sf := (boundedSquareNormIntegers_finite K B).toFinset
  let ef := (boundedSmallSubfieldIntegers_finite K B).toFinset
  let tf (q : Q) :=
    if Odd (Module.finrank ℚ⟮(β q : K)⟯ K) then
      (squareNormTranslateFiber_finite K (β q) B).toFinset else ∅
  have hsub : sf ⊆ ef ∪ Finset.univ.biUnion tf := by
    intro α hα
    obtain ⟨q, hq⟩ := hcover α ((boundedSquareNormIntegers_finite K B).mem_toFinset.mp hα)
    by_cases hodd : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
    · aesop
    · apply Finset.mem_union_left
      exact (boundedSmallSubfieldIntegers_finite K B).mem_toFinset.mpr
        (even_index_translate_mem_smallSubfield K hnoTwo (β q) hodd hq)
  calc
    _ = sf.card := Set.ncard_eq_toFinset_card _ _
    _ ≤ (ef ∪ Finset.univ.biUnion tf).card := Finset.card_le_card hsub
    _ ≤ ef.card + (Finset.univ.biUnion tf).card := Finset.card_union_le _ _
    _ ≤ ef.card + ∑ q : Q, (tf q).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ _ := by
      rw [← Set.ncard_eq_toFinset_card _ (boundedSmallSubfieldIntegers_finite K B)]
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro q _
      by_cases hodd : Odd (Module.finrank ℚ⟮(β q : K)⟯ K)
      · simp [tf, ite_eq_left hodd]
        rw [← Set.ncard_eq_toFinset_card _ (squareNormTranslateFiber_finite K (β q) B)]
        exact squareNormTranslateFiber_count_le K (β q) (hb q)
      grind

