/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.NormCurveReduction

/-! Integer translates pack each bounded square-norm translation class
into the full archimedean lattice box. This isolates the remaining geometric
lattice-point estimate from the already constructed norm-curve family. -/

namespace CCDN
section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]


/-- Translating representatives of the bounded square-norm translation classes by the integers in
`[-⌊R⌋, ⌊R⌋]` gives distinct algebraic integers bounded by `B + R` at every infinite place, so
the number of classes times `2 * ⌊R⌋ + 1` is at most the number of such integers. -/
theorem boundedSquareNormTranslationClasses_packing (B R : ℝ) :
    (boundedSquareNormTranslationClasses K B).card *
        (2 * ⌊R⌋ + 1).toNat ≤
      (boundedArchimedeanIntegers K (B + R)).ncard := by
  let Q := boundedSquareNormTranslationClasses K B
  let Z := Finset.Icc (-⌊R⌋) ⌊R⌋
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ boundedSquareNormIntegers K B ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    exact ⟨r, (boundedSquareNormIntegers_finite K B).mem_toFinset.mp hr, hq⟩
  choose r hr hq using hex
  have hzbound (z : Z) : |(z.val : ℝ)| ≤ R := by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp z.property
    apply abs_le.mpr
    constructor
    · have hneg : -z.val ≤ ⌊R⌋ := by omega
      have h := Int.le_floor.mp hneg
      grind
    · exact Int.le_floor.mp hu
  let a : Q × Z → 𝓞 K := fun t ↦ r t.1 + (t.2.val : 𝓞 K)
  have ha (t : Q × Z) : a t ∈ boundedArchimedeanIntegers K (B + R) := by
    intro w
    calc
      _ ≤ w ((r t.1 : 𝓞 K) : K) + w t.2.val := w.val.add_le _ _
      _ = w ((r t.1 : 𝓞 K) : K) + |(t.2.val : ℝ)| := by aesop
      _ ≤ _ := add_le_add ((hr t.1).2.1 w) (hzbound t.2)
  have haQ (t : Q × Z) : (a t : IntegerTranslationQuotient K) = t.1.val := by aesop
  have hi : Function.Injective a := by
    rintro ⟨q, z⟩ ⟨q', z'⟩ he
    have hqeq : q = q' := Subtype.ext (by
      rw [← haQ (q, z), ← haQ (q', z'), he])
    have hzeq : z = z' := by aesop
    grind
  let ι : Q × Z → boundedArchimedeanIntegers K (B + R) := fun t ↦ ⟨a t, ha t⟩
  let := (boundedArchimedeanIntegers_finite K (B + R)).fintype
  have hcard := Nat.card_le_card_of_injective ι (fun s t h ↦ hi (congrArg Subtype.val h))
  have hZ : Z.card = (2 * ⌊R⌋ + 1).toNat := by
    simp [Z, Int.card_Icc]
    grind
  simpa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    Set.fintypeCard_eq_ncard, hZ] using hcard

