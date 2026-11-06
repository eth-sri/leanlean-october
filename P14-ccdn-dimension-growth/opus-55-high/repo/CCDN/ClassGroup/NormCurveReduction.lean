/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.TranslateFibers

/-! The bounded square-norm set is partitioned by integer translations.
This constructs a finite norm-curve family. The uniform estimate for the
number of translation classes is a separate lattice theorem. -/

namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The quotient of `𝓞 K` by the additive subgroup of rational integers, whose classes are the
orbits under integer translation. -/
abbrev IntegerTranslationQuotient :=
  (𝓞 K) ⧸ AddSubgroup.zmultiples (1 : 𝓞 K)

variable (B : ℝ)

/-- The finite set of integer-translation classes of the bounded square-norm integers
`boundedSquareNormIntegers K B`. -/
def boundedSquareNormTranslationClasses :
    Finset (IntegerTranslationQuotient K) := by
  exact (boundedSquareNormIntegers_finite K B).toFinset.image
    (fun α : 𝓞 K ↦ (α : IntegerTranslationQuotient K))

theorem exists_norm_translate_cover :
    ∃ β : (boundedSquareNormTranslationClasses K B) → 𝓞 K,
      (∀ q, ∀ w : InfinitePlace K, w (β q : K) ≤ B) ∧
      ∀ α ∈ boundedSquareNormIntegers K B,
        ∃ q, α ∈ squareNormTranslateFiber K (β q) B := by
  let S := boundedSquareNormIntegers K B
  let Q := boundedSquareNormTranslationClasses K B
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ S ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  let β : Q → 𝓞 K := fun q ↦ -r q
  have hb (q : Q) (w : InfinitePlace K) : w (β q : K) ≤ B := by
    change w.val (-((r q : 𝓞 K) : K)) ≤ B
    rw [AbsoluteValue.map_neg]
    exact (hr q).2.1 w
  refine ⟨β, hb, ?_⟩
  intro α hα
  have hαf := (boundedSquareNormIntegers_finite K B).mem_toFinset.mpr hα
  let q : Q := ⟨α,
    Finset.mem_image.mpr ⟨α, hαf, rfl⟩⟩
  have he :=
    (hq q).symm
  obtain ⟨x, hx⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (QuotientAddGroup.eq_iff_sub_mem.mp he)
  have hx' : x = α - r q := by grind
  refine ⟨q, hα, x, ?_⟩
  change α = algebraMap ℤ (𝓞 K) x - -r q
  change (algebraMap ℤ (𝓞 K) x) = α - r q at hx'
  rw [hx']
  abel

