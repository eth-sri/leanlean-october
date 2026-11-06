/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.IntegerTranslationClassPacking
import CCDN.ClassGroup.SeparatedIntegerPacking

/-! Bounded algebraic integers lying in an intermediate field
inject into the bounded integers of that field. Every archimedean place
of the subfield is obtained by restricting an ambient place. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic integers of `K` bounded by `B` at every infinite place that lie in the
intermediate field `L`. -/
def boundedIntegersInSubfield (L : IntermediateField ℚ K) (B : ℝ) : Set (𝓞 K) :=
  {β | β ∈ boundedArchimedeanIntegers K B ∧ (β : K) ∈ L}

/-- The set `boundedIntegersInSubfield K L B` is finite. -/
lemma boundedIntegersInSubfield_finite (L : IntermediateField ℚ K) (B : ℝ) :
    (boundedIntegersInSubfield K L B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset (fun _ h ↦ h.1)

/-- For `B ≥ 0`, the number of algebraic integers of `K` bounded by `B` at every infinite place and
lying in `L` is at most `(2 * √m * B + 1) ^ m`, where `m = [L : ℚ]`. -/
theorem boundedIntegersInSubfield_count (L : IntermediateField ℚ K)
    {B : ℝ} (hB : 0 ≤ B) :
    ((boundedIntegersInSubfield K L B).ncard : ℝ) ≤
      (2 * Real.sqrt (Module.finrank ℚ L) * B + 1) ^ Module.finrank ℚ L := by
  /- The map sending a bounded algebraic integer of `K` lying in `L` to the same element viewed as a
  bounded algebraic integer of `L`; every infinite place of `L` is restricted from one of `K`. -/
  /- The map `boundedIntegerToSubfield` does not change the underlying element of `K`. -/
  let := (boundedIntegersInSubfield_finite K L B).fintype
  let := (boundedArchimedeanIntegers_finite L B).fintype
  let toSub : boundedIntegersInSubfield K L B → boundedArchimedeanIntegers L B := fun β ↦
    ⟨⟨⟨(β.val : K), β.property.2⟩,
      (isIntegral_algebraMap_iff (R := ℤ) (A := L) (B := K)).mp β.val.isIntegral_coe⟩, fun w ↦ by
      obtain ⟨v, rfl⟩ := InfinitePlace.comap_surjective (K := K) w
      exact β.property.1 v⟩
  have hle : (boundedIntegersInSubfield K L B).ncard ≤
      (boundedArchimedeanIntegers L B).ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using
      Fintype.card_le_of_injective toSub fun x y h =>
        Subtype.ext (RingOfIntegers.coe_injective
          (congrArg (fun z : boundedArchimedeanIntegers L B ↦ ((z.val : L) : K)) h))
  exact (Nat.cast_le.mpr hle).trans (boundedArchimedeanIntegers_separated_count L hB)

end
end CCDN
