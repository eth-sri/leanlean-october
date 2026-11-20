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

/-- The map sending a bounded algebraic integer of `K` lying in `L` to the same element viewed as a
bounded algebraic integer of `L`; every infinite place of `L` is restricted from one of `K`. -/
private def boundedIntegerToSubfield (L : IntermediateField ℚ K) (B : ℝ) :
    boundedIntegersInSubfield K L B → boundedArchimedeanIntegers L B := fun β ↦ by
  let γ : L := ⟨(β.val : K), β.property.2⟩
  have hγ : γ ∈ integralClosure ℤ L := by
    change IsIntegral ℤ γ
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := L) (B := K)).mp
    exact β.val.isIntegral_coe
  refine ⟨⟨γ, hγ⟩, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := InfinitePlace.comap_surjective (K := K) w
  exact β.property.1 v

/-- For `B ≥ 0`, the number of algebraic integers of `K` bounded by `B` at every infinite place and
lying in `L` is at most `(2 * √m * B + 1) ^ m`, where `m = [L : ℚ]`. -/
theorem boundedIntegersInSubfield_count (L : IntermediateField ℚ K)
    {B : ℝ} (hB : 0 ≤ B) :
    ((boundedIntegersInSubfield K L B).ncard : ℝ) ≤
      (2 * Real.sqrt (Module.finrank ℚ L) * B + 1) ^ Module.finrank ℚ L := by
  let : Finite (boundedArchimedeanIntegers L B) := (boundedArchimedeanIntegers_finite L B).to_subtype
  apply le_trans _ (boundedArchimedeanIntegers_separated_count L hB)
  rw [Nat.cast_le, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  apply Nat.card_le_card_of_injective (boundedIntegerToSubfield K L B)
  intro x y h
  exact Subtype.ext (RingOfIntegers.coe_injective
    (congrArg (fun z : boundedArchimedeanIntegers L B ↦ ((z.val : L) : K)) h))

end
end CCDN
