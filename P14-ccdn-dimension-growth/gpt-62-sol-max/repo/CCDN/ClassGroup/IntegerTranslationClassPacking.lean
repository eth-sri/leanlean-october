/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NormCurveReduction
public import CCDN.Height.Box

/-! Integer translates pack each bounded square-norm translation class
into the full archimedean lattice box. This isolates the remaining geometric
lattice-point estimate from the already constructed norm-curve family. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- Translating representatives of the bounded square-norm translation classes by the integers in
`[-⌊R⌋, ⌊R⌋]` gives distinct algebraic integers bounded by `B + R` at every infinite place, so
the number of classes times `2 * ⌊R⌋ + 1` is at most the number of such integers. -/
theorem boundedSquareNormTranslationClasses_packing (B R : ℝ) :
    (boundedSquareNormTranslationClasses K B).card *
        (integerInterval R).card ≤
      (boundedArchimedeanIntegers K (B + R)).ncard := by
  classical
  let Q := boundedSquareNormTranslationClasses K B
  let Z := integerInterval R
  obtain ⟨r, hr, hq⟩ := exists_squareNorm_translation_representatives K B
  have hzbound (z : Z) : |(z.val : ℝ)| ≤ R := mem_integerInterval.mp z.property
  let a : Q × Z → 𝓞 K := fun t ↦ r t.1 + (t.2.val : 𝓞 K)
  have ha (t : Q × Z) : a t ∈ boundedArchimedeanIntegers K (B + R) := by
    intro w
    change w.val (((r t.1 : 𝓞 K) : K) + (t.2.val : K)) ≤ _
    calc
      _ ≤ w ((r t.1 : 𝓞 K) : K) + w (t.2.val : K) := w.val.add_le _ _
      _ = w ((r t.1 : 𝓞 K) : K) + |(t.2.val : ℝ)| := by
        rw [w.map_intCast, Int.norm_eq_abs]
      _ ≤ _ := add_le_add ((hr t.1).2.1 w) (hzbound t.2)
  have haQ (t : Q × Z) : (a t : IntegerTranslationQuotient K) = t.1.val := by
    simp [a, hq]
  have hi : Function.Injective a := by
    rintro ⟨q, z⟩ ⟨q', z'⟩ he
    have hqeq : q = q' := Subtype.ext (by
      rw [← haQ (q, z), ← haQ (q', z'), he])
    subst q'
    have hzeq : z = z' := by
      exact Subtype.ext (Int.cast_injective (add_left_cancel he))
    subst z'
    rfl
  let ι : Q × Z → boundedArchimedeanIntegers K (B + R) := fun t ↦ ⟨a t, ha t⟩
  have hι : Function.Injective ι := fun s t h ↦ hi (congrArg Subtype.val h)
  let := (boundedArchimedeanIntegers_finite K (B + R)).fintype
  have hcard := Nat.card_le_card_of_injective ι hι
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe,
    Set.fintypeCard_eq_ncard] using hcard

end
end CCDN
