module

public import ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Group.Units.Hom

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

namespace ValuationTheory

/-!
# Finite extensions of discretely valued fields

The extension relation is ambient data: an algebra, finite-dimensionality, and
mathlib's `Valuation.HasExtension` property.  There is deliberately no
proof-irrelevant marker object.  All invariants and maps are defined once for
`DVF` values and can therefore be used unchanged for Henselian and complete
discretely valued fields through their canonical `toDVF` projections.
-/

noncomputable section

universe u v w x

namespace DiscreteValuationField
namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The field degree of a finite valued extension. -/
def degree (_base : DVF.{u, v} K) (_target : DVF.{w, x} L) : ℕ :=
  Module.finrank K L

omit [FiniteDimensional K L]
    [base.valuation.HasExtension target.valuation] in
/-- The degree of a finite extension of discrete valuation fields is its linear `finrank`. -/
@[simp] theorem degree_eq_finrank :
    degree base target = Module.finrank K L :=
  rfl

/-- The canonical ramification index of the target maximal ideal over the
base maximal ideal. -/
noncomputable def ramificationIndex : ℕ :=
  Ideal.ramificationIdx'
    (base.maximalIdeal : Ideal base.valuationSubring)
    (target.maximalIdeal : Ideal target.valuationSubring)

/-- The canonical residue degree of the target maximal ideal over the base
maximal ideal. -/
noncomputable def residueDegree : ℕ :=
  (target.maximalIdeal : Ideal target.valuationSubring).inertiaDeg
    base.valuationSubring

/-- The induced map between valuation subrings. -/
def integerMap :
    base.valuationSubring →+* target.valuationSubring :=
  algebraMap base.valuationSubring target.valuationSubring

omit [FiniteDimensional K L] in
/-- The induced map between valuation subrings is injective. -/
theorem integerMap_injective :
    Function.Injective (integerMap base target) := by
  change Function.Injective
    (algebraMap base.valuation.valuationSubring
      target.valuation.valuationSubring)
  exact _root_.Valuation.HasExtension.algebraMap_injective
    (vK := base.valuation) (vA := target.valuation)

omit [FiniteDimensional K L] in
/-- The valuation-subring map evaluates through the ambient algebra map. -/
@[simp] theorem integerMap_apply (a : base.valuationSubring) :
    (((integerMap base target) a : target.valuationSubring) : L) =
      algebraMap K L (a : K) := by
  change ((algebraMap base.valuation.valuationSubring
    target.valuation.valuationSubring) a : L) = algebraMap K L (a : K)
  rfl



omit [FiniteDimensional K L] in
/-- Maximal-ideal membership is reflected by a valued extension. -/
theorem integerMap_mem_maximalIdeal_iff (a : base.valuationSubring) :
    integerMap base target a ∈ target.maximalIdeal ↔
      a ∈ base.maximalIdeal := by
  rw [target.mem_maximalIdeal_iff (integerMap base target a),
    base.mem_maximalIdeal_iff a, integerMap_apply base target a]
  exact _root_.Valuation.HasExtension.val_map_lt_one_iff
    (vR := base.valuation) (vA := target.valuation) (a : K)





omit [FiniteDimensional K L] in
/-- The target maximal ideal pulls back to the base maximal ideal. -/
theorem maximalIdeal_comap_integerMap_eq :
    target.maximalIdeal.comap (integerMap base target) =
      base.maximalIdeal := by
  ext a
  exact integerMap_mem_maximalIdeal_iff base target a

omit [FiniteDimensional K L] in
/-- The image of the source maximal ideal in the target valuation ring is nonzero. -/
theorem maximalIdeal_map_integerMap_ne_bot :
    Ideal.map (integerMap base target) base.maximalIdeal ≠ ⊥ := by
  intro h
  exact base.maximalIdeal_ne_bot
    ((Ideal.map_eq_bot_iff_of_injective
      (integerMap_injective base target)).1 h)

omit [FiniteDimensional K L] in
/-- The source maximal ideal maps into the target maximal ideal. -/
theorem maximalIdeal_map_integerMap_le :
    Ideal.map (integerMap base target) base.maximalIdeal ≤
      target.maximalIdeal := by
  rw [Ideal.map_le_iff_le_comap,
    maximalIdeal_comap_integerMap_eq base target]

/- A valued extension preserves the residue-field characteristic. -/


/-- The induced map on residue fields. -/
def residueMap :
    base.residueField →+* target.residueField :=
  algebraMap base.residueField target.residueField

omit [FiniteDimensional K L] in
/-- The residue-field map sends the residue of an integer to its target residue. -/
@[simp] theorem residueMap_residue (a : base.valuationSubring) :
    residueMap base target (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  change
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
      (_root_.IsLocalRing.residue base.valuation.valuationSubring a) =
    _root_.IsLocalRing.residue target.valuation.valuationSubring
      ((algebraMap base.valuation.valuationSubring
        target.valuation.valuationSubring) a)
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field map of a valued extension is injective. -/
theorem residueMap_injective :
    Function.Injective (residueMap base target) := by
  change Function.Injective
    (algebraMap
      (_root_.IsLocalRing.ResidueField base.valuation.valuationSubring)
      (_root_.IsLocalRing.ResidueField target.valuation.valuationSubring))
  rw [ValuationTheory.DiscreteValuationField.ResidueField.algebraMap_eq_map_algebraMap]
  exact ValuationTheory.DiscreteValuationField.ResidueField.map_algebraMap_injective









omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map upgrades its canonical injectivity to
bijectivity. -/
theorem residueMap_bijective_of_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective (residueMap base target) :=
  ⟨residueMap_injective base target, hSurj⟩

omit [FiniteDimensional K L] in
/-- The residue-field isomorphism attached to a surjective residue map. -/
noncomputable def residueFieldEquivOfSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueField ≃+* target.residueField :=
  RingEquiv.ofBijective (residueMap base target)
    (residueMap_bijective_of_surjective base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-field equivalence induced by surjectivity evaluates by the residue map. -/
@[simp] theorem residueFieldEquivOfSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    residueFieldEquivOfSurjective base target hSurj z =
      residueMap base target z :=
  rfl

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence recovers a source class after applying the residue map. -/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_residueMap
    (hSurj : Function.Surjective (residueMap base target))
    (z : base.residueField) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (residueMap base target z) = z := by
  simpa using
    (residueFieldEquivOfSurjective base target hSurj).symm_apply_apply z

omit [FiniteDimensional K L] in
/-- Applying the residue map after the inverse residue-field equivalence recovers
the target class. -/
@[simp] theorem residueMap_residueFieldEquivOfSurjective_symm_apply
    (hSurj : Function.Surjective (residueMap base target))
    (z : target.residueField) :
    residueMap base target
        ((residueFieldEquivOfSurjective base target hSurj).symm z) = z :=
  (residueFieldEquivOfSurjective base target hSurj).apply_symm_apply z































/-- The induced map on unit groups of valuation rings. -/
def unitMap :
    base.valuationSubringˣ →* target.valuationSubringˣ :=
  Units.map (integerMap base target).toMonoidHom

omit [FiniteDimensional K L] in
/-- The induced unit map agrees with the valuation-ring map on underlying elements. -/
@[simp] theorem unitMap_apply (a : base.valuationSubringˣ) :
    ((unitMap base target a : target.valuationSubringˣ) :
        target.valuationSubring) =
      integerMap base target (a : base.valuationSubring) :=
  rfl

omit [FiniteDimensional K L] in
/-- The induced map on residue-field units is injective. -/
theorem residueUnitsMap_injective :
    Function.Injective
      (Units.map (residueMap base target).toMonoidHom) :=
  Units.map_injective (residueMap_injective base target)

omit [FiniteDimensional K L] in
/-- Surjectivity of the residue map implies surjectivity on residue-field units. -/
theorem residueUnitsMap_surjective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Surjective
      (Units.map (residueMap base target).toMonoidHom) := by
  intro y
  obtain ⟨z, hz⟩ := hSurj (y : target.residueField)
  have hz0 : z ≠ 0 := by
    intro h
    exact y.ne_zero (by simpa [h] using hz.symm)
  refine ⟨Units.mk0 z hz0, ?_⟩
  apply Units.ext
  simpa using hz

omit [FiniteDimensional K L] in
/-- A surjective residue map induces a bijection on residue-field units. -/
theorem residueUnitsMap_bijective_of_residueMap_surjective
    (hSurj : Function.Surjective (residueMap base target)) :
    Function.Bijective
      (Units.map (residueMap base target).toMonoidHom) :=
  ⟨residueUnitsMap_injective base target,
    residueUnitsMap_surjective_of_residueMap_surjective base target hSurj⟩

omit [FiniteDimensional K L] in
/-- The unit-group equivalence induced by a surjective residue map. -/
noncomputable def residueUnitsEquivOfResidueMapSurjective
    (hSurj : Function.Surjective (residueMap base target)) :
    base.residueFieldˣ ≃* target.residueFieldˣ :=
  MulEquiv.ofBijective (Units.map (residueMap base target).toMonoidHom)
    (residueUnitsMap_bijective_of_residueMap_surjective
      base target hSurj)

omit [FiniteDimensional K L] in
/-- The residue-unit equivalence evaluates by the induced residue-unit map. -/
@[simp] theorem residueUnitsEquivOfResidueMapSurjective_apply
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.residueFieldˣ) :
    residueUnitsEquivOfResidueMapSurjective base target hSurj a =
      Units.map (residueMap base target).toMonoidHom a :=
  rfl

omit [FiniteDimensional K L] in
/-- The residue-field equivalence sends a source residue to the corresponding target residue. -/
@[simp] theorem residueFieldEquivOfSurjective_apply_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    residueFieldEquivOfSurjective base target hSurj (base.residueMap a) =
      target.residueMap (integerMap base target a) := by
  rw [residueFieldEquivOfSurjective_apply,
    residueMap_residue]

omit [FiniteDimensional K L] in
/-- The inverse residue-field equivalence sends a target residue back to its source residue. -/
@[simp] theorem residueFieldEquivOfSurjective_symm_apply_target_residue
    (hSurj : Function.Surjective (residueMap base target))
    (a : base.valuationSubring) :
    (residueFieldEquivOfSurjective base target hSurj).symm
        (target.residueMap (integerMap base target a)) =
      base.residueMap a := by
  rw [← residueMap_residue base target,
    residueFieldEquivOfSurjective_symm_apply_residueMap]

/-- Unramified means that the canonical ramification index is one. -/
def IsUnramified : Prop :=
  ramificationIndex base target = 1

/-- Totally ramified means that the canonical residue degree is one. -/
def IsTotallyRamified : Prop :=
  residueDegree base target = 1

/-- Defectlessness is the exact fundamental equality. -/
def IsDefectless : Prop :=
  degree base target =
    ramificationIndex base target * residueDegree base target

end ValuedExtension
end DiscreteValuationField
end
end ValuationTheory
