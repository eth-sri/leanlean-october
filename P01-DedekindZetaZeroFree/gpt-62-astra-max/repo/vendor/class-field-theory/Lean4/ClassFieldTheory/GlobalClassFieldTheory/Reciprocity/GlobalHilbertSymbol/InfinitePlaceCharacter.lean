module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.InfinitePlace
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
public import GaloisCohomology.Kummer.Concrete.SimpleExtension

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Infinite-place Kummer root characters

This file connects the infinite-place Hilbert factor to the Kummer root
character of the actual infinite-place Artin map.  The complex-place branch
is completed here.  The real quadratic action is kept as the next arithmetic
leaf rather than being introduced as an assumption.
-/

open scoped Classical NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory

variable (K : Type) [Field K] [NumberField K]

/-- The Kummer root character of the actual Artin automorphism at an
infinite place. -/
noncomputable def infinitePlaceKummerRootCharacter
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ) :
    nthRootsSubgroup K (n : ℕ) := by
  let L := chosenSimpleKummerExtension K n hnK b
  letI : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  letI : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  letI : NumberField L := NumberField.of_module_finite K L
  exact
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
      (chosenSimpleKummerRootCharacter K n hnK hmu b
        (chosenInfinitePlaceArtinMonoidHom v (Units.map (algebraMap K v.Completion).toMonoidHom a)))

omit [NumberField K] in
private theorem chosenInfinitePlaceArtinMonoidHom_eq_one_of_isComplex
    {L : Type} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : InfinitePlace K) (hv : v.IsComplex) (x : v.Completionˣ) :
    chosenInfinitePlaceArtinMonoidHom (K := K) (L := L) v x = 1 := by
  let w := chosenInfinitePlaceAbove (L := L) v
  have hwUnramified : w.IsUnramified K := by
    apply InfinitePlace.isUnramified_iff.mpr
    apply Or.inr
    rw [(chosenInfinitePlaceAbove_comap v)]
    exact hv
  have hwUnramified' :
      (chosenInfinitePlaceAbove (L := L) v).IsUnramified K := by
    simpa using hwUnramified
  unfold chosenInfinitePlaceArtinMonoidHom
  unfold infinitePlaceArtinMonoidHomOfPlace
  rw [dite_eq_left hwUnramified']
  rfl

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (v : InfinitePlace K) (a b : Kˣ) (hv : v.IsComplex)

include hv in
/-- At a complex place the infinite-place Kummer root character is
trivial. -/
@[simp]
theorem infinitePlaceKummerRootCharacter_eq_one_of_isComplex :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b = 1 := by
  let L := chosenSimpleKummerExtension K n hnK b
  let :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let := NumberField.of_module_finite K L
  let a_v :=
    Units.map (algebraMap K v.Completion).toMonoidHom a
  change
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm
        (chosenSimpleKummerRootCharacter K n hnK hmu b
          (chosenInfinitePlaceArtinMonoidHom
              v a_v)) = 1
  rw [(chosenInfinitePlaceArtinMonoidHom_eq_one_of_isComplex K v hv a_v), map_one, map_one]

include hv in
/-- The Kummer root character and the explicit Hilbert factor agree at every
complex infinite place. -/
theorem infinitePlaceKummerRootCharacter_localGlobal_of_isComplex :
    infinitePlaceKummerRootCharacter K n hnK hmu v a b =
      infinitePlaceHilbertSymbol K n v a b := by
  rw [infinitePlaceKummerRootCharacter_eq_one_of_isComplex
    K n hnK hmu v a b hv]
  exact (infinitePlaceHilbertSymbol_eq_one_of_isComplex K n v a b hv).symm

end Reciprocity
end GlobalClassFieldTheory

end
