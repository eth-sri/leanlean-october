/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ClassGroup.TwoTorsion
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-! The group-theoretic part of quadratic class-group descent. An
involution on an elementary abelian two-group has at least the square
root of the group's cardinality in fixed points. This is applied to the
action of a field involution on two-torsion ideal classes. -/

@[expose] public section
namespace CCDN
noncomputable section
open NumberField
open scoped NumberField

variable (K : Type*) [Field K]

/-- The action of a field automorphism on two-torsion ideal classes. -/
def classGroupTwoTorsionAction (σ : K ≃+* K) :
    classGroupTwoTorsion K →* classGroupTwoTorsion K where
  toFun c := ⟨ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c, by
    change (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val) ^ 2 = 1
    rw [← map_pow, show c.val ^ 2 = 1 from c.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)

/-- Two-torsion classes fixed by the specified field automorphism. -/
def fixedClassGroupTwoTorsion (σ : K ≃+* K) : Subgroup (classGroupTwoTorsion K) :=
  (classGroupTwoTorsionAction K σ).eqLocus (MonoidHom.id _)

/-- A two-torsion class lies in the `σ`-fixed subgroup if and only if `σ` maps its underlying ideal
class to itself. -/
@[simp]
theorem mem_fixedClassGroupTwoTorsion (σ : K ≃+* K) (c : classGroupTwoTorsion K) :
    c ∈ fixedClassGroupTwoTorsion K σ ↔
      ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv σ) c.val = c.val :=
  Subtype.ext_iff

variable [NumberField K]

/-- For an involutive automorphism `σ` of `K`, the order of the two-torsion subgroup of the class
group is at most the square of the order of its `σ`-fixed subgroup. -/
theorem classGroupTwoTorsionCard_le_fixed_square (σ : K ≃+* K)
    (hσ : Function.Involutive σ) :
    classGroupTwoTorsionCard K ≤ Nat.card (fixedClassGroupTwoTorsion K σ) ^ 2 := by
  let G := classGroupTwoTorsion K
  let α := classGroupTwoTorsionAction K σ
  have hα : Function.Involutive α := by
    intro c
    apply Subtype.ext
    let ρ := RingOfIntegers.mapRingEquiv σ
    change ClassGroup.map (ρ : 𝓞 K →+* 𝓞 K)
      (show Function.Injective (ρ : 𝓞 K →+* 𝓞 K) from ρ.injective)
      (ClassGroup.map (ρ : 𝓞 K →+* 𝓞 K)
        (show Function.Injective (ρ : 𝓞 K →+* 𝓞 K) from ρ.injective) c.val) = c.val
    rw [ClassGroup.map_map]
    have hh : (ρ : 𝓞 K →+* 𝓞 K).comp (ρ : 𝓞 K →+* 𝓞 K) = RingHom.id (𝓞 K) :=
      RingHom.ext fun x => RingOfIntegers.ext (hσ x)
    simpa only [hh] using ClassGroup.map_id c.val
  let τ : G →* G := (MonoidHom.id G) * α
  have hker : τ.ker ≤ fixedClassGroupTwoTorsion K σ := fun x hx => by
    change x * α x = 1 at hx
    change α x = x
    apply mul_left_cancel (a := x)
    exact hx.trans (by simpa only [pow_two] using (Subtype.ext x.property : x ^ 2 = 1).symm)
  have hrange : τ.range ≤ fixedClassGroupTwoTorsion K σ := by
    rintro x ⟨y, rfl⟩
    change α (y * α y) = y * α y
    rw [map_mul, hα, mul_comm]
  calc
    classGroupTwoTorsionCard K = Nat.card τ.ker * Nat.card τ.range :=
      (Subgroup.card_ker_mul_card_range τ).symm
    _ ≤ Nat.card (fixedClassGroupTwoTorsion K σ) * Nat.card (fixedClassGroupTwoTorsion K σ) :=
      Nat.mul_le_mul (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hker))
        (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hrange))
    _ = Nat.card (fixedClassGroupTwoTorsion K σ) ^ 2 := (pow_two _).symm

end
end CCDN
