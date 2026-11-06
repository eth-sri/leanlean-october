/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.TwoTorsion
import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-! The group-theoretic part of quadratic class-group descent. An
involution on an elementary abelian two-group has at least the square
root of the group's cardinality in fixed points. This is applied to the
action of a field involution on two-torsion ideal classes. -/

namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

theorem two_torsion_card_le_involution_fixed_square
    {G : Type*} [CommGroup G] [Finite G]
    (σ : G →* G) (hσ : Function.Involutive σ) (hG : ∀ x : G, x ^ 2 = 1) :
    Nat.card G ≤ Nat.card (σ.eqLocus (MonoidHom.id G)) ^ 2 := by
  let τ : G →* G := (MonoidHom.id G) * σ
  have hker : τ.ker ≤ σ.eqLocus (MonoidHom.id G) := by
    intro x hx
    apply mul_left_cancel
    exact hx.trans (by simpa [pow_two] using (hG x).symm)
  have hrange : τ.range ≤ σ.eqLocus (MonoidHom.id G) := by
    rintro x ⟨y, rfl⟩
    change σ (y * σ y) = y * σ y
    rw [map_mul, hσ, mul_comm]
  have hk := Nat.card_le_card_of_injective (Subgroup.inclusion hker)
    (Subgroup.inclusion_injective hker)
  have hr := Nat.card_le_card_of_injective (Subgroup.inclusion hrange)
    (Subgroup.inclusion_injective hrange)
  calc
    Nat.card G = Nat.card τ.ker * Nat.card τ.range :=
      (Subgroup.card_ker_mul_card_range τ).symm
    _ ≤ Nat.card (σ.eqLocus (MonoidHom.id G)) *
        Nat.card (σ.eqLocus (MonoidHom.id G)) := Nat.mul_le_mul hk hr
    _ = Nat.card (σ.eqLocus (MonoidHom.id G)) ^ 2 := (pow_two _).symm

theorem classGroup_mulEquiv_involutive
    {R : Type*} [CommRing R] [IsDomain R]
    (σ : R ≃+* R) (hσ : Function.Involutive σ) :
    Function.Involutive (ClassGroup.mulEquiv σ) := by
  intro c
  change ClassGroup.map σ
    (show Function.Injective (σ : R →+* R) from σ.injective)
    (ClassGroup.map (σ : R →+* R)
      (show Function.Injective (σ : R →+* R) from σ.injective) c) = c
  rw [ClassGroup.map_map]
  have hh : (σ : R →+* R).comp (σ : R →+* R) = RingHom.id R :=
    RingHom.ext hσ
  simpa only [hh] using ClassGroup.map_id c

variable (K : Type*) [Field K]

section
variable (σ : K ≃+* K)

/-- The action of a field automorphism on two-torsion ideal classes. -/
def classGroupTwoTorsionAction :
    classGroupTwoTorsion K →* classGroupTwoTorsion K where
  toFun c := ⟨ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c, by
    change (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val) ^ 2 = 1
    rw [← map_pow, show c.val ^ 2 = 1 from c.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)

/-- Two-torsion classes fixed by the specified field automorphism. -/
def fixedClassGroupTwoTorsion : Subgroup (classGroupTwoTorsion K) :=
  (classGroupTwoTorsionAction K σ).eqLocus (MonoidHom.id _)

end

variable [NumberField K]

