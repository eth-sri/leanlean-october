/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.NormCurveReduction

/-! Integer translates pack each bounded square-norm translation class
into the full archimedean lattice box. This isolates the remaining geometric
lattice-point estimate from the already constructed norm-curve family. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField NumberField.InfinitePlace

variable (K : Type*) [Field K] [NumberField K]

variable (B : ℝ)

/-- The set of algebraic integers `α ∈ 𝓞 K` with `w α ≤ B` at every infinite place `w`. -/
def boundedArchimedeanIntegers : Set (𝓞 K) :=
  {α | ∀ w : InfinitePlace K, w α ≤ B}

/-- There are finitely many algebraic integers of `K` bounded by `B` at every infinite place. -/
lemma boundedArchimedeanIntegers_finite :
    (boundedArchimedeanIntegers K B).Finite := by
  apply Set.Finite.of_injOn (f := fun β : 𝓞 K ↦ (β : K))
    (t := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B})
  · intro β hβ
    exact ⟨β.isIntegral_coe, fun φ ↦ hβ (InfinitePlace.mk φ)⟩
  · exact RingOfIntegers.coe_injective.injOn
  · exact Embeddings.finite_of_norm_le K ℂ B

/-- Translating representatives of the bounded square-norm translation classes by the integers in
`[-⌊R⌋, ⌊R⌋]` gives distinct algebraic integers bounded by `B + R` at every infinite place, so
the number of classes times `2 * ⌊R⌋ + 1` is at most the number of such integers. -/
theorem boundedSquareNormTranslationClasses_packing (R : ℝ) :
    (boundedSquareNormTranslationClasses K B).card *
        (2 * ⌊R⌋ + 1).toNat ≤
      (boundedArchimedeanIntegers K (B + R)).ncard := by
  classical
  let Q := boundedSquareNormTranslationClasses K B
  let Z := Finset.Icc (-⌊R⌋) ⌊R⌋
  have hex (q : Q) : ∃ r : 𝓞 K, r ∈ boundedSquareNormIntegers K B ∧
      (r : IntegerTranslationQuotient K) = q.val := by
    obtain ⟨r, hr, hq⟩ := Finset.mem_image.mp q.property
    aesop
  choose r hr hq using hex
  have hzbound (z : Z) : |(z.val : ℝ)| ≤ R := by
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp z.property
    apply abs_le.mpr
    constructor
    · have hneg : -z.val ≤ ⌊R⌋ := by omega
      have h := Int.le_floor.mp hneg
      grind
    · exact Int.le_floor.mp hu
  let a : Q × Z → 𝓞 K := fun t ↦ r t.1 + (t.2.val)
  have ha (t : Q × Z) : a t ∈ boundedArchimedeanIntegers K (B + R) := by
    intro w
    calc
      _ ≤ w _ + w (t.2.val) := w.val.add_le _ _
      _ = w _ + |(t.2.val : ℝ)| := by
        solve_by_elim [w.map_intCast]
      _ ≤ _ := add_le_add ((hr t.1).2.1 w) (hzbound t.2)
  have haQ (t : Q × Z) : (a t : IntegerTranslationQuotient K) = t.1.val := by
    change (r t.1) +
      ((t.2.val : 𝓞 K) : IntegerTranslationQuotient K) = _
    simp [*]
  have hi : Function.Injective a := by
    rintro ⟨q, z⟩ ⟨q', z'⟩ he
    have hqeq : q = q' := Subtype.ext (by
      rw [← haQ (q, z), ← haQ (q', z'), he])
    grind [Subtype.ext, Int.cast_injective, add_left_cancel]
  let := (boundedArchimedeanIntegers_finite K (B + R)).fintype
  have hcard := Nat.card_le_card_of_injective (fun t ↦ ⟨a t, ha t⟩) (fun s t h ↦ hi (congrArg Subtype.val h))
  grind [Int.card_Icc, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe, Set.fintypeCard_eq_ncard]

end
end CCDN
