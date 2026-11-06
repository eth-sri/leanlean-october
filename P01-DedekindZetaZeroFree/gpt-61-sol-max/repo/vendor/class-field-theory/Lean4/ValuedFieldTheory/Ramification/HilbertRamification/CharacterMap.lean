module

public import Mathlib

public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

namespace RamificationTheory

/-!
# Hilbert ramification theory: character-map source

This file records the source lemmas for the canonical map
`I_w -> Hom(Delta / Gamma, lambda*)` in prime-decomposition theory.  We do not
package the final value-group quotient here.  Instead, we prove the pieces
which make the formula

`x ↦ (σ x / x) mod U^1`

independent of the unit and base-unit choices used to represent a value class,
and we identify the ramification group as the subgroup on which all these
classes are trivial.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring


variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

section
variable (A : _root_.ValuationSubring L) (σ : decompositionGroup K A)
include A σ
/-- The unit quotient is multiplicative in the unit argument. -/
theorem automorphismUnitQuotient_mul_arg
     
    (x y : Lˣ) :
    automorphismUnitQuotient K A σ (x * y) =
      automorphismUnitQuotient K A σ x *
        automorphismUnitQuotient K A σ y := by
  ext
  simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm]

/-- The unit quotient is trivial on the unit `1`. -/
theorem automorphismUnitQuotient_one_arg
      :
    automorphismUnitQuotient K A σ 1 = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- A `K`-unit contributes trivially to the unit quotient. -/
theorem automorphismUnitQuotient_algebraMapUnit
      (a : Kˣ) :
    automorphismUnitQuotient K A σ
        (Units.map (algebraMap K L).toMonoidHom a) = 1 := by
  ext
  simp [automorphismUnitQuotient]
end


section
variable (A : _root_.ValuationSubring L) (σ : inertiaGroup K A)
include A σ
/-- Prime-decomposition statement:
an inertia element sends valuation-ring units to the same residue class, hence
its unit quotient on such a unit is principal. -/
theorem inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
     
    {u : Lˣ} (hu : u ∈ A.unitGroup) :
    automorphismUnitQuotient K A (σ : decompositionGroup K A) u ∈
      A.principalUnitGroup := by
  let uA : A.unitGroup := ⟨u, hu⟩
  let eA  :=
    MulSemiringAction.toRingEquiv
      (decompositionGroup K A) A (σ : decompositionGroup K A)
  let qA  :=
    A.unitGroupMulEquiv.symm
      (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA) /
        A.unitGroupMulEquiv uA)
  have hres :
      Units.map (IsLocalRing.residue A).toMonoidHom
          (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA)) =
        Units.map (IsLocalRing.residue A).toMonoidHom
          (A.unitGroupMulEquiv uA) := by
    ext
    change
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv
            (decompositionGroup K A) A (σ : decompositionGroup K A)
              (A.unitGroupMulEquiv uA : A)) =
        IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)
    calc
      IsLocalRing.residue A
          (MulSemiringAction.toRingEquiv
            (decompositionGroup K A) A (σ : decompositionGroup K A)
              (A.unitGroupMulEquiv uA : A)) =
          (σ : decompositionGroup K A) •
            IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) := by
        rfl
      _ = IsLocalRing.residue A (A.unitGroupMulEquiv uA : A) := by
        have hσ :
            residueAction K A (σ : decompositionGroup K A) = 1 :=
          MonoidHom.mem_ker.mp σ.property
        change
          (residueAction K A (σ : decompositionGroup K A))
              (IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)) =
            IsLocalRing.residue A (A.unitGroupMulEquiv uA : A)
        rw [hσ]
        rfl
  have hq : (qA : Lˣ) ∈ A.principalUnitGroup := by
    rw [A.coe_mem_principalUnitGroup_iff (x := qA)]
    rw [MonoidHom.mem_ker]
    change
      Units.map (IsLocalRing.residue A).toMonoidHom
          (Units.mapEquiv eA.toMulEquiv (A.unitGroupMulEquiv uA) /
            A.unitGroupMulEquiv uA) = 1
    rw [map_div, hres]
    simp only [div_eq_mul_inv, mul_inv_cancel]
  have hq_coe :
      (qA : Lˣ) =
        automorphismUnitQuotient K A (σ : decompositionGroup K A) u := by
    ext
    rfl
  rw [← hq_coe]
  exact hq

/-- Prime-decomposition statement:
for `σ ∈ I_w`, the class of `σ x / x` modulo principal units.  This is the
raw class from which the character `χ_σ` is assembled after quotienting the
value group. -/
abbrev inertiaUnitQuotientClass
      (x : Lˣ) :
    Lˣ ⧸ A.principalUnitGroup :=
  QuotientGroup.mk
    (automorphismUnitQuotient K A (σ : decompositionGroup K A) x)

/-- States the theorem `inertiaUnitQuotientClass_eq_one_iff`. -/
@[simp] theorem inertiaUnitQuotientClass_eq_one_iff
      (x : Lˣ) :
    inertiaUnitQuotientClass K A σ x = 1 ↔
      automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
        A.principalUnitGroup :=
  QuotientGroup.eq_one_iff _





























/-- Valuation-ring units map to the trivial raw class. -/
def inertiaUnitQuotientClass_eq_one_of_mem_unitGroup
     
    {u : Lˣ} (hu : u ∈ A.unitGroup)  :=
  (inertiaUnitQuotientClass_eq_one_iff (K := K) A σ u).mpr
    (inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
      (K := K) A σ hu)
end





























































section
variable (A : _root_.ValuationSubring L)
include A
/-- The quotient map `Lˣ/U^1 -> Lˣ/Aˣ`.  It measures the remaining value
class of a raw residue-unit quotient. -/
def principalUnitQuotientToValueClass
      :
    Lˣ ⧸ A.principalUnitGroup →* Lˣ ⧸ A.unitGroup :=
  QuotientGroup.map A.principalUnitGroup A.unitGroup
    (MonoidHom.id Lˣ)
    (by
      intro x hx
      exact A.principal_units_le_units hx)

/-- States the theorem `principalUnitQuotientToValueClass_mk`. -/
@[simp] theorem principalUnitQuotientToValueClass_mk
      (x : Lˣ) :
    principalUnitQuotientToValueClass A
        (QuotientGroup.mk' A.principalUnitGroup x) =
      QuotientGroup.mk' A.unitGroup x :=
  rfl

/-- The value displacement of a decomposition-group automorphism at `x`.  It
is the class of `σ x / x` in the value-class quotient `Lˣ/Aˣ`. -/
abbrev valueDisplacementClass
      (σ : decompositionGroup K A) (x : Lˣ)  :=
  QuotientGroup.mk' A.unitGroup (automorphismUnitQuotient K A σ x)

/-- States the theorem `valueDisplacementClass_eq_one_iff`. -/
@[simp] theorem valueDisplacementClass_eq_one_iff
      (σ : decompositionGroup K A) (x : Lˣ) :
    valueDisplacementClass K A σ x = 1 ↔
      automorphismUnitQuotient K A σ x ∈ A.unitGroup :=
  QuotientGroup.eq_one_iff _

/-- States the theorem `principalUnitQuotientToValueClass_inertiaUnitQuotientClass`. -/
@[simp] theorem principalUnitQuotientToValueClass_inertiaUnitQuotientClass
      (σ : inertiaGroup K A) (x : Lˣ) :
    principalUnitQuotientToValueClass A
        (inertiaUnitQuotientClass K A σ x) =
      valueDisplacementClass K A (σ : decompositionGroup K A) x :=
  rfl

/-- For fixed `σ`, value displacement is a group homomorphism on `Lˣ`. -/
def valueDisplacementHom
      (σ : decompositionGroup K A) :
    Lˣ →* Lˣ ⧸ A.unitGroup where
  toFun x := valueDisplacementClass K A σ x
  map_one' := by
    rw [valueDisplacementClass_eq_one_iff,
      automorphismUnitQuotient_one_arg]
    exact A.unitGroup.one_mem
  map_mul' x y := by
    show
      QuotientGroup.mk' A.unitGroup
          (automorphismUnitQuotient K A σ (x * y)) =
        QuotientGroup.mk' A.unitGroup
            (automorphismUnitQuotient K A σ x) *
          QuotientGroup.mk' A.unitGroup
            (automorphismUnitQuotient K A σ y)
    rw [automorphismUnitQuotient_mul_arg]
    apply map_mul

/-- States the theorem `valueDisplacementHom_apply`. -/
@[simp] theorem valueDisplacementHom_apply
      (σ : decompositionGroup K A) (x : Lˣ) :
    valueDisplacementHom K A σ x =
      valueDisplacementClass K A σ x :=
  rfl












/-- In the valuation-subring model, the inertia elements whose value
displacement is trivial.  For the chosen-valuation decomposition group
this condition is automatic; for mathlib's stabilizer of the valuation subring
it is the exact source needed to turn the raw `Lˣ/U^1` class into a residue
field unit. -/
def valueTrivialInertiaGroup
      :
    Subgroup (inertiaGroup K A) where
  carrier :=
    {σ | ∀ x : Lˣ,
      valueDisplacementClass K A (σ : decompositionGroup K A) x = 1}
  one_mem' := by
    intro x
    rw [valueDisplacementClass_eq_one_iff,
      show ((1 : inertiaGroup K A) : decompositionGroup K A) = 1 by rfl,
      automorphismUnitQuotient_one]
    exact A.unitGroup.one_mem
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [valueDisplacementClass_eq_one_iff]
    rw [show
      ((σ * τ : inertiaGroup K A) : decompositionGroup K A) =
        (σ : decompositionGroup K A) * (τ : decompositionGroup K A) by rfl]
    rw [automorphismUnitQuotient_mul]
    exact A.unitGroup.mul_mem
      ((valueDisplacementClass_eq_one_iff (K := K) A
          (σ : decompositionGroup K A)
          (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv)
            x)).mp
        (hσ _))
      ((valueDisplacementClass_eq_one_iff (K := K) A
          (τ : decompositionGroup K A) x).mp
        (hτ x))
  inv_mem' := by
    intro σ hσ x
    rw [valueDisplacementClass_eq_one_iff]
    let y  :=
      (Units.mapEquiv
        (((σ⁻¹ : inertiaGroup K A) :
          decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x
    have hy  :=
      (valueDisplacementClass_eq_one_iff (K := K) A
        (σ : decompositionGroup K A) y).mp (hσ y)
    have hquot :
        automorphismUnitQuotient K A
            ((σ⁻¹ : inertiaGroup K A) : decompositionGroup K A) x =
          (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ := by
      ext
      simp [automorphismUnitQuotient, y, div_eq_mul_inv]
    rw [hquot]
    exact A.unitGroup.inv_mem hy
end










section
variable (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
include A σ
/-- For a value-trivial inertia element, the quotient `σ x / x` is an actual
unit of the valuation ring. -/
def valueTrivialAutomorphismUnit
      (x : Lˣ) :
    A.unitGroup :=
  ⟨automorphismUnitQuotient K A
      ((σ : inertiaGroup K A) : decompositionGroup K A) x,
    (valueDisplacementClass_eq_one_iff (K := K) A
      ((σ : inertiaGroup K A) : decompositionGroup K A) x).mp
      (σ.property x)⟩

/-- States the theorem `valueTrivialAutomorphismUnit_coe`. -/
@[simp] theorem valueTrivialAutomorphismUnit_coe
      (x : Lˣ) :
    (valueTrivialAutomorphismUnit K A σ x : Lˣ) =
      automorphismUnitQuotient K A
        ((σ : inertiaGroup K A) : decompositionGroup K A) x :=
  rfl

/-- States the theorem `valueTrivialAutomorphismUnit_one_arg`. -/
@[simp] theorem valueTrivialAutomorphismUnit_one_arg
      :
    valueTrivialAutomorphismUnit K A σ 1 = 1 := by
  ext
  simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_one_arg]

/-- States the theorem `valueTrivialAutomorphismUnit_mul_arg`. -/
theorem valueTrivialAutomorphismUnit_mul_arg
      (x y : Lˣ) :
    valueTrivialAutomorphismUnit K A σ (x * y) =
      valueTrivialAutomorphismUnit K A σ x *
        valueTrivialAutomorphismUnit K A σ y := by
  ext
  simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_mul_arg]

/-- The character `χ_σ` is defined by:
for value-trivial inertia, `x ↦ σ x / x mod P` is a homomorphism
`Lˣ -> λˣ`. -/
def valueTrivialInertiaResidueUnitHom
      :
    Lˣ →* (IsLocalRing.ResidueField A)ˣ where
  toFun x :=
    A.unitGroupToResidueFieldUnits
      (valueTrivialAutomorphismUnit K A σ x)
  map_one' := by
    rw [valueTrivialAutomorphismUnit_one_arg]
    exact map_one A.unitGroupToResidueFieldUnits
  map_mul' x y := by
    rw [valueTrivialAutomorphismUnit_mul_arg]
    apply map_mul

/-- States the theorem `valueTrivialInertiaResidueUnitHom_apply`. -/
@[simp] theorem valueTrivialInertiaResidueUnitHom_apply
      (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A σ x =
      A.unitGroupToResidueFieldUnits
        (valueTrivialAutomorphismUnit K A σ x) :=
  rfl

/-- Valuation-ring units are killed by the residue-unit character. -/
theorem unitGroup_le_valueTrivialInertiaResidueUnitHom_ker
      :
    A.unitGroup ≤ (valueTrivialInertiaResidueUnitHom K A σ).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, valueTrivialInertiaResidueUnitHom_apply]
  let uA  := valueTrivialAutomorphismUnit K A σ u
  have hprincipal  :=
    inertia_automorphismUnitQuotient_mem_principalUnitGroup_of_mem_unitGroup
      (K := K) A (σ : inertiaGroup K A) hu
  have hker : uA ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [A.ker_unitGroupToResidueFieldUnits]
    change (uA : Lˣ) ∈ A.principalUnitGroup
    simpa [uA, valueTrivialAutomorphismUnit] using hprincipal
  change A.unitGroupToResidueFieldUnits uA = 1
  exact MonoidHom.mem_ker.mp hker

/-- Base-field units are killed by the residue-unit character. -/
theorem valueTrivialInertiaResidueUnitHom_baseUnit
      (a : Kˣ) :
    valueTrivialInertiaResidueUnitHom K A σ
        (Units.map (algebraMap K L).toMonoidHom a) = 1 := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  let uA  :=
    valueTrivialAutomorphismUnit K A σ
      (Units.map (algebraMap K L).toMonoidHom a)
  have hprincipal :
      automorphismUnitQuotient K A
          ((σ : inertiaGroup K A) : decompositionGroup K A)
          (Units.map (algebraMap K L).toMonoidHom a) ∈
        A.principalUnitGroup := by
    rw [automorphismUnitQuotient_algebraMapUnit]
    exact A.principalUnitGroup.one_mem
  have hker : uA ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [A.ker_unitGroupToResidueFieldUnits]
    change (uA : Lˣ) ∈ A.principalUnitGroup
    simpa [uA, valueTrivialAutomorphismUnit] using hprincipal
  change A.unitGroupToResidueFieldUnits uA = 1
  exact MonoidHom.mem_ker.mp hker
end


section
variable (A : _root_.ValuationSubring L)
include A
/-- A value-trivial inertia element changes a unit representative only by a
valuation-ring unit, hence every residue-unit character is unchanged after
applying it to the representative. -/
theorem valueTrivialInertiaResidueUnitHom_mapEquiv_arg
     
    (σ τ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A σ
        (Units.mapEquiv
          ((((τ : inertiaGroup K A) : decompositionGroup K A) :
            L ≃ₐ[K] L).toMulEquiv) x) =
      valueTrivialInertiaResidueUnitHom K A σ x := by
  let q  :=
    automorphismUnitQuotient K A
      ((τ : inertiaGroup K A) : decompositionGroup K A) x
  have hq_mem : q ∈ A.unitGroup :=
    (valueDisplacementClass_eq_one_iff (K := K) A
      ((τ : inertiaGroup K A) : decompositionGroup K A) x).mp
      (τ.property x)
  have harg :
      Units.mapEquiv
          ((((τ : inertiaGroup K A) : decompositionGroup K A) :
            L ≃ₐ[K] L).toMulEquiv) x =
        q * x := by
    ext
    simp [q, automorphismUnitQuotient, div_eq_mul_inv, mul_comm]
  rw [harg, map_mul]
  have hq :
      valueTrivialInertiaResidueUnitHom K A σ q = 1 :=
    MonoidHom.mem_ker.mp
      (unitGroup_le_valueTrivialInertiaResidueUnitHom_ker
        (K := K) A σ hq_mem)
  rw [hq, one_mul]

/-- The identity inertia element gives the trivial residue-unit character. -/
theorem valueTrivialInertiaResidueUnitHom_one
      (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A
        (1 : valueTrivialInertiaGroup K A) x = 1 := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  have hunit :
      valueTrivialAutomorphismUnit K A
          (1 : valueTrivialInertiaGroup K A) x = 1 := by
    ext
    simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_one]
  rw [hunit]
  exact map_one A.unitGroupToResidueFieldUnits

/-- Prime-decomposition statement:
the residue-unit characters multiply with the inertia element. -/
theorem valueTrivialInertiaResidueUnitHom_mul
     
    (σ τ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A (σ * τ) x =
      valueTrivialInertiaResidueUnitHom K A σ x *
        valueTrivialInertiaResidueUnitHom K A τ x := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  have hunit :
      valueTrivialAutomorphismUnit K A (σ * τ) x =
        valueTrivialAutomorphismUnit K A σ
          (Units.mapEquiv
            ((((τ : inertiaGroup K A) : decompositionGroup K A) :
              L ≃ₐ[K] L).toMulEquiv) x) *
        valueTrivialAutomorphismUnit K A τ x := by
    ext
    simp [valueTrivialAutomorphismUnit, automorphismUnitQuotient_mul]
  rw [hunit, map_mul]
  change
    valueTrivialInertiaResidueUnitHom K A σ
        (Units.mapEquiv
          ((((τ : inertiaGroup K A) : decompositionGroup K A) :
            L ≃ₐ[K] L).toMulEquiv) x) *
      valueTrivialInertiaResidueUnitHom K A τ x =
    valueTrivialInertiaResidueUnitHom K A σ x *
      valueTrivialInertiaResidueUnitHom K A τ x
  rw [valueTrivialInertiaResidueUnitHom_mapEquiv_arg]

/-- Prime-decomposition statement:
the residue-unit character descends from representatives `x : Lˣ` to value
classes modulo valuation-ring units. -/
def valueClassToResidueUnits
     
    (σ : valueTrivialInertiaGroup K A)  :=
  QuotientGroup.lift A.unitGroup
    (valueTrivialInertiaResidueUnitHom K A σ)
    (unitGroup_le_valueTrivialInertiaResidueUnitHom_ker (K := K) A σ)

/-- States the theorem `valueClassToResidueUnits_mk`. -/
@[simp] theorem valueClassToResidueUnits_mk
     
    (σ : valueTrivialInertiaGroup K A) (x : Lˣ) :
    valueClassToResidueUnits K A σ
        (QuotientGroup.mk' A.unitGroup x) =
      valueTrivialInertiaResidueUnitHom K A σ x :=
  rfl

/-- States the theorem `valueTrivialInertiaResidueUnitHom_eq_one_of_mem_ramificationGroup`. -/
theorem valueTrivialInertiaResidueUnitHom_eq_one_of_mem_ramificationGroup
     
    (σ : valueTrivialInertiaGroup K A)
    (hσ : (σ : inertiaGroup K A) ∈ ramificationGroup K A)
    (x : Lˣ) :
    valueTrivialInertiaResidueUnitHom K A σ x = 1 := by
  rw [valueTrivialInertiaResidueUnitHom_apply]
  let uA  := valueTrivialAutomorphismUnit K A σ x
  have hprincipal  :=
    (mem_ramificationGroup_iff (K := K) A (σ : inertiaGroup K A)).mp hσ x
  have hker : uA ∈ A.unitGroupToResidueFieldUnits.ker := by
    rw [A.ker_unitGroupToResidueFieldUnits]
    change (uA : Lˣ) ∈ A.principalUnitGroup
    simpa [uA, valueTrivialAutomorphismUnit] using hprincipal
  change A.unitGroupToResidueFieldUnits uA = 1
  exact MonoidHom.mem_ker.mp hker

/-- Prime-decomposition statement:
for fixed `σ ∈ I_w`, the raw unit quotient is a group homomorphism
`Lˣ -> Lˣ / U^1`. -/
def inertiaUnitQuotientHom
      (σ : inertiaGroup K A) :
    Lˣ →* Lˣ ⧸ A.principalUnitGroup where
  toFun x := inertiaUnitQuotientClass K A σ x
  map_one' := by
    rw [inertiaUnitQuotientClass_eq_one_iff,
      automorphismUnitQuotient_one_arg]
    exact A.principalUnitGroup.one_mem
  map_mul' x y := by
    show
      QuotientGroup.mk' A.principalUnitGroup
          (automorphismUnitQuotient K A
            (σ : decompositionGroup K A) (x * y)) =
        QuotientGroup.mk' A.principalUnitGroup
            (automorphismUnitQuotient K A
              (σ : decompositionGroup K A) x) *
          QuotientGroup.mk' A.principalUnitGroup
            (automorphismUnitQuotient K A
              (σ : decompositionGroup K A) y)
    rw [automorphismUnitQuotient_mul_arg]
    apply map_mul

/-- States the theorem `inertiaUnitQuotientHom_apply`. -/
@[simp] theorem inertiaUnitQuotientHom_apply
      (σ : inertiaGroup K A) (x : Lˣ) :
    inertiaUnitQuotientHom K A σ x =
      inertiaUnitQuotientClass K A σ x :=
  rfl











/-- The raw quotient homomorphism kills the valuation-ring unit group. -/
theorem unitGroup_le_inertiaUnitQuotientHom_ker
      (σ : inertiaGroup K A) :
    A.unitGroup ≤ (inertiaUnitQuotientHom K A σ).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, inertiaUnitQuotientHom_apply]
  apply inertiaUnitQuotientClass_eq_one_of_mem_unitGroup <;> assumption

/-- Prime-decomposition statement:
the raw character descends from representatives `x : Lˣ` to value classes
modulo valuation-ring units.  This is the quotient layer corresponding to
`Delta = w(L*)`. -/
def valueClassToPrincipalUnitQuotient
      (σ : inertiaGroup K A)  :=
  QuotientGroup.lift A.unitGroup
    (inertiaUnitQuotientHom K A σ)
    (unitGroup_le_inertiaUnitQuotientHom_ker (K := K) A σ)

/-- States the theorem `valueClassToPrincipalUnitQuotient_mk`. -/
@[simp] theorem valueClassToPrincipalUnitQuotient_mk
      (σ : inertiaGroup K A) (x : Lˣ) :
    valueClassToPrincipalUnitQuotient K A σ
        (QuotientGroup.mk' A.unitGroup x) =
      inertiaUnitQuotientClass K A σ x :=
  rfl

/-- The image of base-field units in `Lˣ / A.unitGroup`.  This is the
subgroup that later realizes `Gamma` inside `Delta`. -/
def baseUnitToValueClass    :=
  (QuotientGroup.mk' A.unitGroup).comp
    (Units.map (algebraMap K L).toMonoidHom)

/-- States the theorem `baseUnitToValueClass_apply`. -/
@[simp] theorem baseUnitToValueClass_apply
      (a : Kˣ) :
    baseUnitToValueClass K A a =
      QuotientGroup.mk' A.unitGroup
        (Units.map (algebraMap K L).toMonoidHom a) :=
  rfl

/-- The subgroup of `Lˣ/A.unitGroup` generated by base-field value classes. -/
abbrev baseUnitValueClassSubgroup    :=
  (baseUnitToValueClass K A).range
end


/-- Provides the instance `baseUnitValueClassSubgroup_normal`. -/
instance baseUnitValueClassSubgroup_normal
    (A : _root_.ValuationSubring L) :
    (baseUnitValueClassSubgroup K A).Normal :=
  ⟨by
    intro n hn g
    have hconj : g * n * g⁻¹ = n := by
      rw [mul_comm g n, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn⟩

section
variable (A : _root_.ValuationSubring L) (σ : inertiaGroup K A)
include A σ
/-- Base-field units map trivially under the descended raw character. -/
theorem valueClassToPrincipalUnitQuotient_baseUnit
      (a : Kˣ) :
    valueClassToPrincipalUnitQuotient K A σ
        (baseUnitToValueClass K A a) = 1 := by
  rw [baseUnitToValueClass_apply, valueClassToPrincipalUnitQuotient_mk]
  exact (inertiaUnitQuotientClass_eq_one_iff
    (K := K) A σ (Units.map (algebraMap K L).toMonoidHom a)).mpr (by
      rw [automorphismUnitQuotient_algebraMapUnit]
      exact A.principalUnitGroup.one_mem)

/-- The base-field value classes lie in the kernel of the descended raw
character. -/
theorem baseUnitValueClassSubgroup_le_valueClassToPrincipalUnitQuotient_ker
      :
    baseUnitValueClassSubgroup K A ≤
      (valueClassToPrincipalUnitQuotient K A σ).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker]
  apply valueClassToPrincipalUnitQuotient_baseUnit

/-- Prime-decomposition statement:
the raw character descends further modulo the base value group.  This quotient
is the group-theoretic model of `Delta/Gamma` before identifying it with a
concrete value-group quotient. -/
def valueModuloBaseToPrincipalUnitQuotient
       :=
  QuotientGroup.lift (baseUnitValueClassSubgroup K A)
    (valueClassToPrincipalUnitQuotient K A σ)
    (baseUnitValueClassSubgroup_le_valueClassToPrincipalUnitQuotient_ker
      (K := K) A σ)

/-- States the theorem `valueModuloBaseToPrincipalUnitQuotient_mk`. -/
@[simp] theorem valueModuloBaseToPrincipalUnitQuotient_mk
     
    (x : Lˣ ⧸ A.unitGroup) :
    valueModuloBaseToPrincipalUnitQuotient K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A) x) =
      valueClassToPrincipalUnitQuotient K A σ x :=
  rfl

/-- States the theorem `valueModuloBaseToPrincipalUnitQuotient_mk_mk`. -/
@[simp] theorem valueModuloBaseToPrincipalUnitQuotient_mk_mk
      (x : Lˣ) :
    valueModuloBaseToPrincipalUnitQuotient K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
          (QuotientGroup.mk' A.unitGroup x)) =
      inertiaUnitQuotientClass K A σ x :=
  rfl
end


section
variable (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
include A σ
/-- The base value classes are killed by the residue-unit character. -/
theorem baseUnitValueClassSubgroup_le_valueClassToResidueUnits_ker
      :
    baseUnitValueClassSubgroup K A ≤
      (valueClassToResidueUnits K A σ).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, baseUnitToValueClass_apply,
    valueClassToResidueUnits_mk]
  apply valueTrivialInertiaResidueUnitHom_baseUnit

/-- Prime-decomposition statement:
the residue-unit character on `Delta/Gamma`, modeled as
`(Lˣ/Aˣ)/(Kˣ)`, for value-trivial inertia. -/
def valueModuloBaseToResidueUnits
       :=
  QuotientGroup.lift (baseUnitValueClassSubgroup K A)
    (valueClassToResidueUnits K A σ)
    (baseUnitValueClassSubgroup_le_valueClassToResidueUnits_ker
      (K := K) A σ)

/-- States the theorem `valueModuloBaseToResidueUnits_mk`. -/
@[simp] theorem valueModuloBaseToResidueUnits_mk
      (x : Lˣ ⧸ A.unitGroup) :
    valueModuloBaseToResidueUnits K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A) x) =
      valueClassToResidueUnits K A σ x :=
  rfl

/-- States the theorem `valueModuloBaseToResidueUnits_mk_mk`. -/
@[simp] theorem valueModuloBaseToResidueUnits_mk_mk
      (x : Lˣ) :
    valueModuloBaseToResidueUnits K A σ
        (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
          (QuotientGroup.mk' A.unitGroup x)) =
      valueTrivialInertiaResidueUnitHom K A σ x :=
  rfl

/-- The inertia-character construction satisfies:
an element of `R_w` gives the trivial residue-unit character on
`Delta/Gamma`.  This is the kernel direction for the canonical map from
inertia to `Hom(Delta/Gamma, lambda*)`. -/
theorem valueModuloBaseToResidueUnits_eq_one_of_mem_ramificationGroup
     
    (hσ : (σ : inertiaGroup K A) ∈ ramificationGroup K A) :
    valueModuloBaseToResidueUnits K A σ = 1 := by
  apply QuotientGroup.monoidHom_ext
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply,
    valueModuloBaseToResidueUnits_mk_mk,
    MonoidHom.one_apply]
  apply valueTrivialInertiaResidueUnitHom_eq_one_of_mem_ramificationGroup <;> assumption
end


/-- prime-decomposition theory:
`σ ↦ χ_σ`, realized on the group-theoretic model of `Delta/Gamma`.

For mathlib's valuation-subring stabilizer this is stated on the value-trivial
inertia subgroup; for a chosen valuation in the exact-extension sense this is the
ordinary inertia group. -/
def valueTrivialInertiaCharacterHom
    (A : _root_.ValuationSubring L) :
    valueTrivialInertiaGroup K A →*
      ((Lˣ ⧸ A.unitGroup) ⧸ baseUnitValueClassSubgroup K A →*
        (IsLocalRing.ResidueField A)ˣ) where
  toFun σ := valueModuloBaseToResidueUnits K A σ
  map_one' := by
    apply QuotientGroup.monoidHom_ext
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply,
      valueModuloBaseToResidueUnits_mk_mk,
      MonoidHom.one_apply]
    apply valueTrivialInertiaResidueUnitHom_one
  map_mul' σ τ := by
    apply QuotientGroup.monoidHom_ext
    apply QuotientGroup.monoidHom_ext
    apply MonoidHom.ext
    intro x
    show
      valueModuloBaseToResidueUnits K A (σ * τ)
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
            (QuotientGroup.mk' A.unitGroup x)) =
        valueModuloBaseToResidueUnits K A σ
            (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
              (QuotientGroup.mk' A.unitGroup x)) *
          valueModuloBaseToResidueUnits K A τ
            (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
              (QuotientGroup.mk' A.unitGroup x))
    rw [valueModuloBaseToResidueUnits_mk_mk,
      valueModuloBaseToResidueUnits_mk_mk,
      valueModuloBaseToResidueUnits_mk_mk]
    apply valueTrivialInertiaResidueUnitHom_mul

section
variable (A : _root_.ValuationSubring L)
    (σ : valueTrivialInertiaGroup K A)
include A σ
/-- States the theorem `valueTrivialInertiaCharacterHom_apply`. -/
@[simp] theorem valueTrivialInertiaCharacterHom_apply
      :
    valueTrivialInertiaCharacterHom K A σ =
      valueModuloBaseToResidueUnits K A σ :=
  rfl

/-- The ramification group is contained in the kernel of the character map. -/
theorem valueTrivialInertiaCharacterHom_mem_ker_of_mem_ramificationGroup
     
    (hσ : (σ : inertiaGroup K A) ∈ ramificationGroup K A) :
    σ ∈ (valueTrivialInertiaCharacterHom K A).ker := by
  rw [MonoidHom.mem_ker, valueTrivialInertiaCharacterHom_apply]
  apply valueModuloBaseToResidueUnits_eq_one_of_mem_ramificationGroup <;> assumption

/-- Conversely, a value-trivial inertia element with trivial character lies in
the ramification group. -/
theorem mem_ramificationGroup_of_valueTrivialInertiaCharacterHom_mem_ker
     
    (hσ : σ ∈ (valueTrivialInertiaCharacterHom K A).ker) :
    (σ : inertiaGroup K A) ∈ ramificationGroup K A := by
  rw [mem_ramificationGroup_iff]
  intro x
  have hchar :
      valueModuloBaseToResidueUnits K A σ
          (QuotientGroup.mk' (baseUnitValueClassSubgroup K A)
            (QuotientGroup.mk' A.unitGroup x)) = 1 := by
    simp_all
  have hres :
      A.unitGroupToResidueFieldUnits
          (valueTrivialAutomorphismUnit K A σ x) = 1 := by
    rw [valueModuloBaseToResidueUnits_mk_mk] at hchar
    simpa only [valueTrivialInertiaResidueUnitHom_apply] using hchar
  have hker  :=
    MonoidHom.mem_ker.mpr hres
  rw [A.ker_unitGroupToResidueFieldUnits] at hker
  have hker' :
      (valueTrivialAutomorphismUnit K A σ x : Lˣ) ∈
        A.principalUnitGroup := hker
  simpa [valueTrivialAutomorphismUnit] using hker'

/-- Prime-decomposition statement:
on value-trivial inertia, the kernel of `σ ↦ χ_σ` is exactly `R_w`. -/
theorem valueTrivialInertiaCharacterHom_mem_ker_iff
      :
    σ ∈ (valueTrivialInertiaCharacterHom K A).ker ↔
      (σ : inertiaGroup K A) ∈ ramificationGroup K A := by
  constructor
  · apply mem_ramificationGroup_of_valueTrivialInertiaCharacterHom_mem_ker
  · apply valueTrivialInertiaCharacterHom_mem_ker_of_mem_ramificationGroup
end


end ValuationSubring
end HilbertRamification

end
end RamificationTheory
