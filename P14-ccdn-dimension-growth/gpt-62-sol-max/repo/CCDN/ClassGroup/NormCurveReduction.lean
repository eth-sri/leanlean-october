/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.TranslateFibers
import Mathlib.Data.Set.Card.Arithmetic

/-! The bounded square-norm set is partitioned by integer translations.
This constructs a finite norm-curve family. The uniform estimate for the
number of translation classes is a separate lattice theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The quotient of `𝓞 K` by the additive subgroup of rational integers, whose classes are the
orbits under integer translation. -/
abbrev IntegerTranslationQuotient :=
  (𝓞 K) ⧸ AddSubgroup.zmultiples (1 : 𝓞 K)

/-- The finite set of integer-translation classes of the bounded square-norm integers
`boundedSquareNormIntegers K B`. -/
def boundedSquareNormTranslationClasses (B : ℝ) :
    Finset (IntegerTranslationQuotient K) := by
  classical
  exact (boundedSquareNormIntegers_finite K B).toFinset.image
    (fun α : 𝓞 K ↦ (α : IntegerTranslationQuotient K))

/-- Choose a bounded representative of each integer-translation class. -/
lemma exists_squareNorm_translation_representatives (B : ℝ) :
    ∃ r : boundedSquareNormTranslationClasses K B → 𝓞 K,
      (∀ q, r q ∈ boundedSquareNormIntegers K B) ∧
      ∀ q, (r q : IntegerTranslationQuotient K) = q.val := by
  have h (q : boundedSquareNormTranslationClasses K B) :
      ∃ x ∈ boundedSquareNormIntegers K B, (x : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨x, hx, hq⟩ := Finset.mem_image.mp q.property
    aesop
  choose r hr hq using h
  exact ⟨r, hr, hq⟩

/-- Representatives for the bounded translation classes and a cover by their fibers. -/
private theorem exists_norm_translate_cover (B : ℝ) :
    ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
      (∀ q, ∀ w : InfinitePlace K, w (β q : K) ≤ B) ∧
      ∀ α ∈ boundedSquareNormIntegers K B,
        ∃ q, α ∈ squareNormTranslateFiber K (β q) B := by
  let Q := boundedSquareNormTranslationClasses K B
  obtain ⟨r, hr, hq⟩ := exists_squareNorm_translation_representatives K B
  let β := fun q ↦ -r q
  have hb (q : Q) (w : InfinitePlace K) : w (β q : K) ≤ B := by
    change w.val (-((r q : 𝓞 K) : K)) ≤ B
    rw [AbsoluteValue.map_neg]
    exact (hr q).2.1 w
  refine ⟨β, hb, ?_⟩
  intro α hα
  let q : Q := ⟨(α : IntegerTranslationQuotient K),
    Finset.mem_image.mpr ⟨α, ((boundedSquareNormIntegers_finite K B).mem_toFinset.mpr hα), rfl⟩⟩
  obtain ⟨x, hx⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (QuotientAddGroup.eq_iff_sub_mem.mp ((hq q).symm))
  refine ⟨q, hα, x, ?_⟩
  simpa [β] using sub_eq_iff_eq_add.mp (by simpa using hx.symm)

/-- Count the two signed norm curves per translation class. Fibers outside the chosen
predicate are counted together in the exceptional set `E`. -/
theorem squareNorm_count_le_of_curves
    {B C : ℝ} (hC : 0 ≤ C) (E : Set (𝓞 K)) (hE : E.Finite) (P : 𝓞 K → Prop)
    (hex : ∀ β, ¬ P β → squareNormTranslateFiber K β B ⊆ E)
    (hc : ∀ (β : 𝓞 K) (ε : ℤ), P β → IsUnit ε →
      (count (signedNormCurveLocus K β ε)
        (max (2 * B) (Real.sqrt (B ^ Module.finrank ℚ K))) : ℝ) ≤ C) :
    ((boundedSquareNormIntegers K B).ncard : ℝ) ≤
      E.ncard + 2 * C * (boundedSquareNormTranslationClasses K B).card := by
  classical
  obtain ⟨β, hb, hcover⟩ := exists_norm_translate_cover K B
  let F (q : boundedSquareNormTranslationClasses K B) :=
    if P (β q) then squareNormTranslateFiber K (β q) B else ∅
  have hF (q) : (F q).Finite := by
    dsimp [F]
    split
    · exact squareNormTranslateFiber_finite K (β q) B
    · exact Set.finite_empty
  have hsub : boundedSquareNormIntegers K B ⊆ E ∪ ⋃ q, F q := by
    intro x hx
    obtain ⟨q, hq⟩ := hcover x hx
    by_cases hp : P (β q)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨q, by simpa [F, hp]⟩)
    · exact Or.inl (hex _ hp hq)
  have hsum :=
    (Set.ncard_le_ncard hsub (hE.union (Set.finite_iUnion hF))).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype _) _))
  have hf (q) : ((F q).ncard : ℝ) ≤ 2 * C := by
    by_cases hp : P (β q)
    · have h := squareNormTranslateFiber_count_le K (β q) (hb q)
      have h' := Nat.cast_le (α := ℝ).mpr h
      simp only [F, ite_eq_left hp]
      push_cast at h'
      have h1 := hc (β q) 1 hp isUnit_one
      have h2 := hc (β q) (-1) hp (by simp)
      linarith
    · simpa [F, hp] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC
  calc
    _ ≤ E.ncard + ∑ q, ((F q).ncard : ℝ) := by exact_mod_cast hsum
    _ ≤ E.ncard + ∑ _q : boundedSquareNormTranslationClasses K B, 2 * C := by gcongr; exact hf _
    _ = _ := by simp [mul_comm]

end
end CCDN
