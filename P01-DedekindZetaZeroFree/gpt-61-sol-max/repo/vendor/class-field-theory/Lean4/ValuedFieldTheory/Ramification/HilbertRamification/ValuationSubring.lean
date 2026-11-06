module

public import Mathlib

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

namespace RamificationTheory

/-!
# Hilbert ramification theory: valuation-subring layer

This file manages the ordinary valuation-subring decomposition/inertia exact
sequence.  For an arbitrary valuation subring the residue action need not be
onto the full residue automorphism group; the canonical theorem is the exact
sequence with target equal to the range of the residue action.
-/

noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- finite Galois ramification theory:
the decomposition group of a valuation subring. -/
abbrev decompositionGroup (A : _root_.ValuationSubring L)  :=
  A.decompositionSubgroup K

/-- finite Galois ramification theory:
the inertia group of a valuation subring. -/
abbrev inertiaGroup (A : _root_.ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  A.inertiaSubgroup K

/-- The residue action of the decomposition group on the residue field. -/
abbrev residueAction (A : _root_.ValuationSubring L)  :=
  MulSemiringAction.toRingAut
    (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- The inertia group is the kernel of the residue action. -/
theorem residueAction_ker (A : _root_.ValuationSubring L) :
    MonoidHom.ker (residueAction K A) = inertiaGroup K A := rfl

/-- Provides the instance `inertiaGroup_normal`. -/
instance inertiaGroup_normal (A : _root_.ValuationSubring L) :
    (inertiaGroup K A).Normal := by
  rw [← residueAction_ker (K := K) A]
  infer_instance

section
variable (A : _root_.ValuationSubring L)
include A
/-- finite Galois ramification theory:
the unit quotient `σ x / x` attached to an automorphism in the decomposition
group.  This is the expression used in the definition of the ramification
group. -/
def automorphismUnitQuotient
      (σ : decompositionGroup K A) (x : Lˣ)  :=
  Units.mapEquiv ((σ : L ≃ₐ[K] L).toMulEquiv) x / x

/-- States the theorem `automorphismUnitQuotient_one`. -/
@[simp] theorem automorphismUnitQuotient_one
      (x : Lˣ) :
    automorphismUnitQuotient K A 1 x = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- States the theorem `automorphismUnitQuotient_mul`. -/
theorem automorphismUnitQuotient_mul
      (σ τ : decompositionGroup K A) (x : Lˣ) :
    automorphismUnitQuotient K A (σ * τ) x =
      automorphismUnitQuotient K A σ
        (Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) x) *
      automorphismUnitQuotient K A τ x := by
  ext
  simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]

/-- The decomposition and inertia subgroup definitions:
the ramification group `R_w`, as the subgroup of inertia whose unit quotients
`σ x / x` are principal units for every `x : Lˣ`. -/
def ramificationGroup   :
    Subgroup (inertiaGroup K A) where
  carrier :=
    {σ | ∀ x : Lˣ,
      automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
        A.principalUnitGroup}
  one_mem' := by
    intro x
    have hmap : Units.mapEquiv (AlgEquiv.toMulEquiv (1 : L ≃ₐ[K] L)) x = x := by
      ext
      rfl
    simp [automorphismUnitQuotient, hmap]
  mul_mem' := by
    intro σ τ hσ hτ x
    change
      automorphismUnitQuotient K A ((σ * τ : inertiaGroup K A) : decompositionGroup K A) x ∈
        A.principalUnitGroup
    have hx :
        automorphismUnitQuotient K A (σ : decompositionGroup K A)
            (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x) *
          automorphismUnitQuotient K A (τ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
      A.principalUnitGroup.mul_mem
      (hσ (Units.mapEquiv (((τ : decompositionGroup K A) : L ≃ₐ[K] L).toMulEquiv) x))
      (hτ x)
    simpa [automorphismUnitQuotient_mul] using hx
  inv_mem' := by
    intro σ hσ x
    let y  :=
      Units.mapEquiv
        ((((σ : decompositionGroup K A)⁻¹ : decompositionGroup K A) :
          L ≃ₐ[K] L).toMulEquiv) x
    have hy  :=
      hσ y
    have hyinv :
        (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ ∈
          A.principalUnitGroup :=
      A.principalUnitGroup.inv_mem hy
    have hquot :
        automorphismUnitQuotient K A
            ((σ⁻¹ : inertiaGroup K A) : decompositionGroup K A) x =
          (automorphismUnitQuotient K A (σ : decompositionGroup K A) y)⁻¹ := by
      ext
      simp [automorphismUnitQuotient, y, div_eq_mul_inv]
    rw [hquot]
    exact hyinv

/-- States the theorem `mem_ramificationGroup_iff`. -/
@[simp] theorem mem_ramificationGroup_iff
      (σ : inertiaGroup K A) :
    σ ∈ ramificationGroup K A ↔
      ∀ x : Lˣ,
        automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
  Iff.rfl


/-- finite Galois ramification theory:
the decomposition field `Z_w` is the fixed field of the decomposition group. -/
abbrev decompositionField    :=
  IntermediateField.fixedField (decompositionGroup K A)









/-- The inertia group as a subgroup of the full `K`-automorphism group of `L`.
This is the subgroup whose fixed field is the classical inertia field. -/
abbrev inertiaGroupInAut    :=
  Subgroup.map (decompositionGroup K A).subtype (inertiaGroup K A)

/-- The canonical inclusion `I_w -> G(L/K)`. -/
def inertiaGroupToAut    :=
  (decompositionGroup K A).subtype.comp (inertiaGroup K A).subtype

/-- States the theorem `inertiaGroupToAut_apply`. -/
@[simp] theorem inertiaGroupToAut_apply
      (σ : inertiaGroup K A) :
    inertiaGroupToAut (K := K) A σ =
      ((σ : decompositionGroup K A) : L ≃ₐ[K] L) :=
  rfl

/-- The inertia-field definition:
the inertia field `T_w` is the fixed field of the inertia group. -/
abbrev inertiaField    :=
  IntermediateField.fixedField (inertiaGroupInAut K A)















/-- The inertia subgroup, viewed inside the full automorphism group, lies in
the decomposition group. -/
theorem inertiaGroupInAut_le_decompositionGroup
      :
    inertiaGroupInAut K A ≤ decompositionGroup K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact τ.property

/-- The ramification group as a subgroup of the full automorphism group. -/
abbrev ramificationGroupInAut    :=
  Subgroup.map (inertiaGroupToAut (K := K) A) (ramificationGroup K A)

/-- The ramification-field definition:
the ramification field `V_w` is the fixed field of the ramification group. -/
abbrev ramificationField    :=
  IntermediateField.fixedField (ramificationGroupInAut K A)
















/-- The ramification subgroup, viewed in `G(L/K)`, lies in inertia. -/
theorem ramificationGroupInAut_le_inertiaGroupInAut
      :
    ramificationGroupInAut K A ≤ inertiaGroupInAut K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩

/-- finite Galois ramification theory:
the inertia field is contained in the ramification field. -/
def inertiaField_le_ramificationField
       :=
  IntermediateField.fixedField_le
    (ramificationGroupInAut_le_inertiaGroupInAut (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the inertia field
`T_w`. -/
abbrev ramificationFieldOverInertiaField
       :=
  IntermediateField.extendScalars
    (inertiaField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverInertiaField_restrictScalars`. -/
@[simp] theorem ramificationFieldOverInertiaField_restrictScalars
      :
    (ramificationFieldOverInertiaField K A).restrictScalars K =
      ramificationField K A :=
  rfl






























/-- finite Galois ramification theory:
the decomposition field is contained in the inertia field. -/
def decompositionField_le_inertiaField
       :=
  IntermediateField.fixedField_le
    (inertiaGroupInAut_le_decompositionGroup (K := K) A)

/-- finite Galois ramification theory:
the decomposition field is contained in the ramification field. -/
def decompositionField_le_ramificationField
       :=
  (decompositionField_le_inertiaField (K := K) A).trans
    (inertiaField_le_ramificationField (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `V_w | Z_w`. -/
abbrev ramificationFieldOverDecompositionField
       :=
  IntermediateField.extendScalars
    (decompositionField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverDecompositionField_restrictScalars`. -/
@[simp] theorem ramificationFieldOverDecompositionField_restrictScalars
      :
    (ramificationFieldOverDecompositionField K A).restrictScalars K =
      ramificationField K A :=
  rfl

/-- The inertia-field definition source:
the inertia field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `G(T_w/Z_w)`. -/
abbrev inertiaFieldOverDecompositionField
       :=
  IntermediateField.extendScalars
    (decompositionField_le_inertiaField (K := K) A)









/-- States the theorem `inertiaFieldOverDecompositionField_restrictScalars`. -/
@[simp] theorem inertiaFieldOverDecompositionField_restrictScalars
      :
    (inertiaFieldOverDecompositionField K A).restrictScalars K =
      inertiaField K A :=
  rfl
end









/-- The fixed-field description of decomposition source:
the decomposition group is the Galois group over its fixed field. -/
def decompositionGroupEquivGalDecompositionField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)  :=
  IntermediateField.subgroupEquivAlgEquiv (decompositionGroup K A)









/--
States the theorem `decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply`.
-/
@[simp] theorem decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : decompositionGroup K A) (x : L) :
    decompositionGroupEquivGalDecompositionField_of_finiteDimensional (K := K) A σ x =
      ((σ : L ≃ₐ[K] L) x) :=
  rfl



















































































































































section IntermediateFieldFunctoriality

variable {M : Type*} [Field M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L]

/-- Restrict scalars on automorphisms along an intermediate field
`K ⊆ M ⊆ L`.  This is the inclusion `G(L/M) -> G(L/K)` used in
scalar-restriction compatibility of ramification subgroups. -/
def restrictAutomorphismScalars : (L ≃ₐ[M] L) →* (L ≃ₐ[K] L) where
  toFun σ :=
    { σ with
      commutes' := by
        intro a
        simp [IsScalarTower.algebraMap_eq K M L, σ.commutes (algebraMap K M a)] }
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl



























































































































































end IntermediateFieldFunctoriality









/-- The ordinary valuation-subring first-isomorphism form:
`D/I` is the range of the residue action. -/
def quotientInertiaEquivResidueActionRange
    (A : _root_.ValuationSubring L)  :=
  (QuotientGroup.quotientMulEquivOfEq
      (residueAction_ker K A).symm).trans
    (QuotientGroup.quotientKerEquivRange (residueAction K A))

/-- States the theorem `quotientInertiaEquivResidueActionRange_mk`. -/
@[simp] theorem quotientInertiaEquivResidueActionRange_mk
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) :
    quotientInertiaEquivResidueActionRange (K := K) A
        (QuotientGroup.mk' (inertiaGroup K A) σ) =
      (residueAction K A).rangeRestrict σ :=
  rfl














end ValuationSubring
end HilbertRamification

end
end RamificationTheory
