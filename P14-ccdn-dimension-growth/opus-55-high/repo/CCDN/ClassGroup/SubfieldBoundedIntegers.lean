/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.IntegerTranslationClassPacking
import CCDN.ClassGroup.SeparatedIntegerPacking

/-! Bounded algebraic integers lying in an intermediate field
inject into the bounded integers of that field. Every archimedean place
of the subfield is obtained by restricting an ambient place. -/

namespace CCDN
section
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

section
variable (L : IntermediateField ℚ K) (B : ℝ)

/-- The algebraic integers of `K` bounded by `B` at every infinite place that lie in the
intermediate field `L`. -/
def boundedIntegersInSubfield : Set (𝓞 K) :=
  {β | β ∈ boundedArchimedeanIntegers K B ∧ (β : K) ∈ L}

/-- The set `boundedIntegersInSubfield K L B` is finite. -/
lemma boundedIntegersInSubfield_finite :
    (boundedIntegersInSubfield K L B).Finite :=
  (boundedArchimedeanIntegers_finite K B).subset (fun _ h ↦ h.1)

/-- The map sending a bounded algebraic integer of `K` lying in `L` to the same element viewed as a
bounded algebraic integer of `L`; every infinite place of `L` is restricted from one of `K`. -/
def boundedIntegerToSubfield :
    boundedIntegersInSubfield K L B → boundedArchimedeanIntegers L B := fun β ↦ by
  let γ : L := ⟨(β.val : K), β.property.2⟩
  have hγ : γ ∈ integralClosure ℤ L := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := L) (B := K)).mp
    exact β.val.isIntegral_coe
  let z : 𝓞 L := ⟨γ, hγ⟩
  refine ⟨z, ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := InfinitePlace.comap_surjective (K := K) w
  rw [comap_apply]
  rw [show (z : L) = γ from RingOfIntegers.coe_mk hγ]
  exact β.property.1 v

/-- The map `boundedIntegerToSubfield` does not change the underlying element of `K`. -/
@[simp] lemma boundedIntegerToSubfield_coe
    (β : boundedIntegersInSubfield K L B) :
    (((boundedIntegerToSubfield K L B β).val : L) : K) = (β.val : K) := by
  rfl

theorem boundedIntegersInSubfield_ncard_le :
    (boundedIntegersInSubfield K L B).ncard ≤
      (boundedArchimedeanIntegers L B).ncard := by
  let := (boundedIntegersInSubfield_finite K L B).fintype
  let := (boundedArchimedeanIntegers_finite L B).fintype
  simpa using
    Fintype.card_le_of_injective (boundedIntegerToSubfield K L B)
      (show Function.Injective (boundedIntegerToSubfield K L B) by
          intro x y h
          apply Subtype.ext
          apply RingOfIntegers.coe_injective
          simpa using
            congrArg (fun z ↦ ((z.val : L) : K)) h)

end

