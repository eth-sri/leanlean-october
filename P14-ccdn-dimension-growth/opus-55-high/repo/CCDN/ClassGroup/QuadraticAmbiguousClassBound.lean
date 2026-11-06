/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ClassGroup.QuadraticInvolution
import CCDN.ClassGroup.QuadraticObstructionFibers
import CCDN.ClassGroup.AmbiguousIdealRelativeNorm
import CCDN.ClassGroup.FractionalIdealConjugation
import CCDN.ClassGroup.QuadraticNormConjugation

/-! A cardinal bound for fixed two-torsion classes in terms of
strongly ambiguous classes and the unit-norm quotient. This is
the obstruction-fiber part of genus theory; the ramified-ideal estimate
for the strongly ambiguous subgroup is a separate step. -/

namespace CCDN
noncomputable section
open NumberField
open scoped NumberField nonZeroDivisors

theorem card_le_subgroup_mul_obstruction
    {G Q : Type*} [CommGroup G] [Finite G] [Finite Q]
    (S : Subgroup G) (o : G → Q)
    (ho : ∀ x y, o x = o y → x / y ∈ S) :
    Nat.card G ≤ Nat.card S * Nat.card Q := by
  let r : G ⧸ S → G := fun x => Classical.choose (QuotientGroup.mk_surjective x)
  have hr : ∀ x : G ⧸ S, QuotientGroup.mk (r x) = x :=
    fun x => Classical.choose_spec (QuotientGroup.mk_surjective x)
  have hc := Nat.card_le_card_of_injective _ (by
    intro x y h
    rw [← hr x, ← hr y]
    apply div_eq_one.mp
    exact (QuotientGroup.eq_one_iff _).mpr (ho _ _ h))
  calc
    Nat.card G = Nat.card S * S.index := S.card_mul_index.symm
    _ ≤ Nat.card S * Nat.card Q := Nat.mul_le_mul_left _ hc

variable (F K : Type*) [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K]

/-- Witness data for an ambiguous ideal class `c` (one fixed by `σ`): an invertible fractional
ideal representing `c`, a scalar comparing it with its conjugate, and a base unit equal to the
relative norm of that scalar. -/
structure AmbiguousClassWitness (σ : K ≃ₐ[F] K) (c : ClassGroup (𝓞 K)) where
  /-- An invertible fractional ideal representing the class. -/
  ideal : (FractionalIdeal (𝓞 K)⁰ K)ˣ
  /-- The scalar comparing the conjugate of `ideal` with `ideal`. -/
  scalar : Kˣ
  /-- A unit of `𝓞 F` equal to the relative norm of `scalar`. -/
  baseUnit : (𝓞 F)ˣ
  /-- The fractional ideal `ideal` represents the class `c`. -/
  class_eq : ClassGroup.mk K ideal = c
  /-- The conjugate of `ideal` under `σ` is the principal ideal of `scalar` times `ideal`. -/
  scalar_eq : fractionalIdealUnitAction (K := K)
    (RingOfIntegers.mapAlgEquiv σ).toRingEquiv ideal =
      toPrincipalIdeal (𝓞 K) K scalar * ideal
  /-- The relative norm of `scalar` is the base unit `baseUnit`. -/
  norm_eq : Algebra.norm F (scalar : K) = ((baseUnit : 𝓞 F) : F)

section
variable (σ : K ≃ₐ[F] K)

theorem nonempty_ambiguousClassWitness (c : ClassGroup (𝓞 K))
    (hc : ClassGroup.mulEquiv (RingOfIntegers.mapAlgEquiv σ).toRingEquiv c = c) :
    Nonempty (AmbiguousClassWitness F K σ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  obtain ⟨x, y, u, hx, hy, hxy, hu⟩ :=
    ambiguous_ideal_scalar_relative_unit (𝓞 F) (𝓞 K) (RingOfIntegers.mapAlgEquiv σ) I hc
  have hn := congrArg (algebraMap (𝓞 F) F) hu
  rw [map_mul, Algebra.algebraMap_intNorm (K := F) (L := K),
    Algebra.algebraMap_intNorm (K := F) (L := K)] at hn
  replace hu : Algebra.norm F ((y : K) / (x : K)) = ((u : 𝓞 F) : F) := by
    rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, ← div_eq_mul_inv]
    apply (div_eq_iff (Algebra.norm_ne_zero_iff.mpr (mod_cast hx))).mpr
    exact hn.symm.trans (mul_comm _ _)
  let a : Kˣ := Units.mk0 x (RingOfIntegers.coe_ne_zero_iff.mpr hx)
  let b : Kˣ := Units.mk0 y (RingOfIntegers.coe_ne_zero_iff.mpr hy)
  refine ⟨⟨FractionalIdeal.mk0 K I, b / a, u,
    ClassGroup.mk_mk0 K I, ?_, ?_⟩⟩
  · exact integral_ideal_scalar_fractional_comparison
      (RingOfIntegers.mapAlgEquiv σ).toRingEquiv I x y hx hy hxy
  · aesop

def chosenAmbiguousClassWitness
    (c : fixedClassGroupTwoTorsion K σ.toRingEquiv) :
    AmbiguousClassWitness F K σ c.val.val :=
  Classical.choice (nonempty_ambiguousClassWitness F K σ c.val.val
    (Subtype.ext_iff.mp c.property))

/-- A fixed choice of the unit-norm obstruction on fixed
two-torsion classes. The cardinal argument only uses equality of values. -/
def fixedClassUnitObstruction :
    fixedClassGroupTwoTorsion K σ.toRingEquiv → quadraticUnitNormQuotient F K :=
  fun c => QuotientGroup.mk (chosenAmbiguousClassWitness F K σ c).baseUnit

end

theorem fixedClassUnitObstruction_eq_implies
    (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
    (c e : fixedClassGroupTwoTorsion K σ.toRingEquiv)
    (hce : fixedClassUnitObstruction F K σ c = fixedClassUnitObstruction F K σ e) :
    c.val.val / e.val.val ∈ stronglyAmbiguousClassGroup F K σ := by
  let w := chosenAmbiguousClassWitness F K σ c
  let z := chosenAmbiguousClassWitness F K σ e
  rw [← w.class_eq, ← z.class_eq]
  exact equal_unit_obstructions_stronglyAmbiguous F K hd σ hσ
    w.ideal z.ideal w.scalar z.scalar w.baseUnit z.baseUnit
    w.scalar_eq z.scalar_eq w.norm_eq z.norm_eq hce

/-- The two-torsion subgroup of the strongly ambiguous subgroup. -/
abbrev stronglyAmbiguousTwoTorsion (σ : K ≃ₐ[F] K) :=
  (powMonoidHom 2 : stronglyAmbiguousClassGroup F K σ →*
    stronglyAmbiguousClassGroup F K σ).ker

variable (hd : Module.finrank F K = 2) (σ : K ≃ₐ[F] K) (hσ : σ ≠ 1)
include hd hσ

theorem fixedClassGroupTwoTorsion_card_le
    :
    Nat.card (fixedClassGroupTwoTorsion K σ.toRingEquiv) ≤
      Nat.card (stronglyAmbiguousTwoTorsion F K σ) *
        Nat.card (quadraticUnitNormQuotient F K) := by
  let emb : fixedClassGroupTwoTorsion K σ.toRingEquiv →* ClassGroup (𝓞 K) :=
    (classGroupTwoTorsion K).subtype.comp (fixedClassGroupTwoTorsion K σ.toRingEquiv).subtype
  let S := (stronglyAmbiguousClassGroup F K σ).comap emb
  let := quadraticUnitNormQuotient_finite F K hd
  have hc := card_le_subgroup_mul_obstruction S (fixedClassUnitObstruction F K σ)
    (fun c e h => fixedClassUnitObstruction_eq_implies F K hd σ hσ c e h)
  let incl : S → stronglyAmbiguousTwoTorsion F K σ := fun c =>
    ⟨⟨c.val.val.val, c.property⟩, by aesop⟩
  have hincl : Function.Injective incl := by
    intro c e h
    grind
  exact hc.trans (Nat.mul_le_mul_right _
    (Nat.card_le_card_of_injective incl hincl))

/-- The quadratic two-torsion count is reduced to the strongly
ambiguous subgroup, with a proved degree-only unit factor. -/
theorem classGroupTwoTorsionCard_le_stronglyAmbiguous
    :
    classGroupTwoTorsionCard K ≤
      (Nat.card (stronglyAmbiguousTwoTorsion F K σ) * 2 ^ Module.finrank ℚ F) ^ 2 := by
  exact (show classGroupTwoTorsionCard K ≤ Nat.card (fixedClassGroupTwoTorsion K σ.toRingEquiv) ^ 2 by
      apply two_torsion_card_le_involution_fixed_square
        (classGroupTwoTorsionAction K σ.toRingEquiv) (show Function.Involutive (classGroupTwoTorsionAction K σ.toRingEquiv) by
            have hσO : Function.Involutive (RingOfIntegers.mapRingEquiv σ.toRingEquiv) := by
              intro x
              exact RingOfIntegers.ext ((quadratic_automorphism_involutive F K hd σ) x)
            intro c
            apply Subtype.ext
            exact classGroup_mulEquiv_involutive _ hσO c)
      intro c
      exact Subtype.ext c.property).trans
      (Nat.pow_le_pow_left ((fixedClassGroupTwoTorsion_card_le F K hd σ hσ).trans
    (Nat.mul_le_mul_left _ (quadraticUnitNormQuotient_card_le_degree F K hd))) 2)

