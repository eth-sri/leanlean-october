module

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
abbrev decompositionGroup (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  A.decompositionSubgroup K

/-- finite Galois ramification theory:
the inertia group of a valuation subring. -/
abbrev inertiaGroup (A : _root_.ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  A.inertiaSubgroup K

/-- The residue action of the decomposition group on the residue field. -/
abbrev residueAction (A : _root_.ValuationSubring L) :
    decompositionGroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- The inertia group is the kernel of the residue action. -/
theorem residueAction_ker (A : _root_.ValuationSubring L) :
    MonoidHom.ker (residueAction K A) = inertiaGroup K A := by
  rfl

/-- Provides the instance `inertiaGroup_normal`. -/
instance inertiaGroup_normal (A : _root_.ValuationSubring L) :
    (inertiaGroup K A).Normal := by
  rw [← residueAction_ker (K := K) A]
  infer_instance

/-- finite Galois ramification theory:
the unit quotient `σ x / x` attached to an automorphism in the decomposition
group.  This is the expression used in the definition of the ramification
group. -/
def automorphismUnitQuotient
    (A : _root_.ValuationSubring L) (σ : decompositionGroup K A) (x : Lˣ) :
    Lˣ :=
  Units.mapEquiv ((σ : L ≃ₐ[K] L).toMulEquiv) x / x

/-- States the theorem `automorphismUnitQuotient_one`. -/
@[simp] theorem automorphismUnitQuotient_one
    (A : _root_.ValuationSubring L) (x : Lˣ) :
    automorphismUnitQuotient K A 1 x = 1 := by
  ext
  simp [automorphismUnitQuotient]

/-- States the theorem `automorphismUnitQuotient_mul`. -/
theorem automorphismUnitQuotient_mul
    (A : _root_.ValuationSubring L) (σ τ : decompositionGroup K A) (x : Lˣ) :
    automorphismUnitQuotient K A (σ * τ) x =
      automorphismUnitQuotient K A σ
        (Units.mapEquiv ((τ : L ≃ₐ[K] L).toMulEquiv) x) *
      automorphismUnitQuotient K A τ x := by
  ext
  simp [automorphismUnitQuotient, div_eq_mul_inv, mul_assoc]

/-- The decomposition and inertia subgroup definitions:
the ramification group `R_w`, as the subgroup of inertia whose unit quotients
`σ x / x` are principal units for every `x : Lˣ`. -/
def ramificationGroup (A : _root_.ValuationSubring L) :
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
    let y : Lˣ :=
      Units.mapEquiv
        ((((σ : decompositionGroup K A)⁻¹ : decompositionGroup K A) :
          L ≃ₐ[K] L).toMulEquiv) x
    have hy :
        automorphismUnitQuotient K A (σ : decompositionGroup K A) y ∈
          A.principalUnitGroup :=
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
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    σ ∈ ramificationGroup K A ↔
      ∀ x : Lˣ,
        automorphismUnitQuotient K A (σ : decompositionGroup K A) x ∈
          A.principalUnitGroup :=
  Iff.rfl


/-- finite Galois ramification theory:
the decomposition field `Z_w` is the fixed field of the decomposition group. -/
abbrev decompositionField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup K A)

/-- States the theorem `mem_decompositionField_iff`. -/
@[simp] theorem mem_decompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ decompositionField K A ↔
      ∀ σ ∈ decompositionGroup K A, σ x = x := by
  exact IntermediateField.mem_fixedField_iff
    (H := decompositionGroup K A) x

/-- The inertia group as a subgroup of the full `K`-automorphism group of `L`.
This is the subgroup whose fixed field is the classical inertia field. -/
abbrev inertiaGroupInAut (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.map (decompositionGroup K A).subtype (inertiaGroup K A)

/-- The canonical inclusion `I_w -> G(L/K)`. -/
def inertiaGroupToAut (A : _root_.ValuationSubring L) :
    inertiaGroup K A →* (L ≃ₐ[K] L) :=
  (decompositionGroup K A).subtype.comp (inertiaGroup K A).subtype

/-- States the theorem `inertiaGroupToAut_apply`. -/
@[simp] theorem inertiaGroupToAut_apply
    (A : _root_.ValuationSubring L) (σ : inertiaGroup K A) :
    inertiaGroupToAut (K := K) A σ =
      ((σ : decompositionGroup K A) : L ≃ₐ[K] L) :=
  rfl

/-- The inertia-field definition:
the inertia field `T_w` is the fixed field of the inertia group. -/
abbrev inertiaField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (inertiaGroupInAut K A)

/-- States the theorem `mem_inertiaField_iff`. -/
@[simp] theorem mem_inertiaField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ inertiaField K A ↔
      ∀ σ : inertiaGroup K A, ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [inertiaField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ
    exact h ((σ : decompositionGroup K A) : L ≃ₐ[K] L)
      ⟨(σ : decompositionGroup K A), σ.property, rfl⟩
  · intro h σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    exact h ⟨τ, hτ⟩

/-- The inertia subgroup, viewed inside the full automorphism group, lies in
the decomposition group. -/
theorem inertiaGroupInAut_le_decompositionGroup
    (A : _root_.ValuationSubring L) :
    inertiaGroupInAut K A ≤ decompositionGroup K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact τ.property

/-- The ramification group as a subgroup of the full automorphism group. -/
abbrev ramificationGroupInAut (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[K] L) :=
  Subgroup.map (inertiaGroupToAut (K := K) A) (ramificationGroup K A)

/-- The ramification-field definition:
the ramification field `V_w` is the fixed field of the ramification group. -/
abbrev ramificationField (A : _root_.ValuationSubring L) :
    IntermediateField K L :=
  IntermediateField.fixedField (ramificationGroupInAut K A)

/-- States the theorem `mem_ramificationField_iff`. -/
@[simp] theorem mem_ramificationField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ ramificationField K A ↔
      ∀ σ : ramificationGroup K A,
        (((σ : inertiaGroup K A) : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [ramificationField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h σ
    exact h (inertiaGroupToAut (K := K) A (σ : inertiaGroup K A))
      ⟨(σ : inertiaGroup K A), σ.property, rfl⟩
  · intro h σ hσ
    rcases hσ with ⟨τ, hτ, rfl⟩
    exact h ⟨τ, hτ⟩

/-- The ramification subgroup, viewed in `G(L/K)`, lies in inertia. -/
theorem ramificationGroupInAut_le_inertiaGroupInAut
    (A : _root_.ValuationSubring L) :
    ramificationGroupInAut K A ≤ inertiaGroupInAut K A := by
  rintro σ ⟨τ, _hτ, rfl⟩
  exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩

/-- finite Galois ramification theory:
the inertia field is contained in the ramification field. -/
theorem inertiaField_le_ramificationField
    (A : _root_.ValuationSubring L) :
    inertiaField K A ≤ ramificationField K A :=
  IntermediateField.fixedField_le
    (ramificationGroupInAut_le_inertiaGroupInAut (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the inertia field
`T_w`. -/
abbrev ramificationFieldOverInertiaField
    (A : _root_.ValuationSubring L) :
    IntermediateField (inertiaField K A) L :=
  IntermediateField.extendScalars
    (inertiaField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverInertiaField_restrictScalars`. -/
@[simp] theorem ramificationFieldOverInertiaField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (ramificationFieldOverInertiaField K A).restrictScalars K =
      ramificationField K A :=
  rfl







/-- finite Galois ramification theory:
the decomposition field is contained in the inertia field. -/
theorem decompositionField_le_inertiaField
    (A : _root_.ValuationSubring L) :
    decompositionField K A ≤ inertiaField K A :=
  IntermediateField.fixedField_le
    (inertiaGroupInAut_le_decompositionGroup (K := K) A)

/-- finite Galois ramification theory:
the decomposition field is contained in the ramification field. -/
theorem decompositionField_le_ramificationField
    (A : _root_.ValuationSubring L) :
    decompositionField K A ≤ ramificationField K A :=
  (decompositionField_le_inertiaField (K := K) A).trans
    (inertiaField_le_ramificationField (K := K) A)

/-- The ramification-field definition source:
the ramification field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `V_w | Z_w`. -/
abbrev ramificationFieldOverDecompositionField
    (A : _root_.ValuationSubring L) :
    IntermediateField (decompositionField K A) L :=
  IntermediateField.extendScalars
    (decompositionField_le_ramificationField (K := K) A)

/-- States the theorem `ramificationFieldOverDecompositionField_restrictScalars`. -/
@[simp] theorem ramificationFieldOverDecompositionField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (ramificationFieldOverDecompositionField K A).restrictScalars K =
      ramificationField K A :=
  rfl

/-- The inertia-field definition source:
the inertia field, viewed as an intermediate field over the decomposition
field `Z_w`.  This is the field appearing in `G(T_w/Z_w)`. -/
abbrev inertiaFieldOverDecompositionField
    (A : _root_.ValuationSubring L) :
    IntermediateField (decompositionField K A) L :=
  IntermediateField.extendScalars
    (decompositionField_le_inertiaField (K := K) A)

/-- States the theorem `mem_inertiaFieldOverDecompositionField_iff`. -/
@[simp] theorem mem_inertiaFieldOverDecompositionField_iff
    (A : _root_.ValuationSubring L) (x : L) :
    x ∈ inertiaFieldOverDecompositionField K A ↔
      ∀ σ : inertiaGroup K A, ((σ : decompositionGroup K A) : L ≃ₐ[K] L) x = x := by
  rw [inertiaFieldOverDecompositionField, IntermediateField.mem_extendScalars,
    mem_inertiaField_iff]

/-- States the theorem `inertiaFieldOverDecompositionField_restrictScalars`. -/
@[simp] theorem inertiaFieldOverDecompositionField_restrictScalars
    (A : _root_.ValuationSubring L) :
    (inertiaFieldOverDecompositionField K A).restrictScalars K =
      inertiaField K A :=
  rfl



/-- The fixed-field description of decomposition source:
the decomposition group is the Galois group over its fixed field. -/
def decompositionGroupEquivGalDecompositionField_of_finiteDimensional
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    decompositionGroup K A ≃* (L ≃ₐ[decompositionField K A] L) :=
  IntermediateField.subgroupEquivAlgEquiv (decompositionGroup K A)

/-- The fixed-field description of decomposition source:
`L/Z_w` is Galois because `Z_w` is the fixed field of the finite
decomposition group action. -/
instance decompositionField_isGalois
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    IsGalois (decompositionField K A) L :=
  IsGalois.of_fixed_field L (decompositionGroup K A)

/--
States the theorem `decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply`.
-/
@[simp] theorem decompositionGroupEquivGalDecompositionField_of_finiteDimensional_apply
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : decompositionGroup K A) (x : L) :
    decompositionGroupEquivGalDecompositionField_of_finiteDimensional (K := K) A σ x =
      ((σ : L ≃ₐ[K] L) x) :=
  rfl

/-- The inertia-field definition source:
the inertia subgroup transported to `Gal(L/Z_w)` through
`G_w = G(L/Z_w)`. -/
abbrev inertiaGroupOverDecompositionField
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    Subgroup (L ≃ₐ[decompositionField K A] L) :=
  Subgroup.map
    (decompositionGroupEquivGalDecompositionField_of_finiteDimensional
      (K := K) A).toMonoidHom
    (inertiaGroup K A)

/-- States the theorem `mem_inertiaGroupOverDecompositionField_iff`. -/
@[simp] theorem mem_inertiaGroupOverDecompositionField_iff
    [FiniteDimensional K L] (A : _root_.ValuationSubring L)
    (σ : L ≃ₐ[decompositionField K A] L) :
    σ ∈ inertiaGroupOverDecompositionField (K := K) A ↔
      ∃ τ : inertiaGroup K A,
        decompositionGroupEquivGalDecompositionField_of_finiteDimensional
          (K := K) A (τ : decompositionGroup K A) = σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨⟨τ, hτ⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨(τ : decompositionGroup K A), τ.property, rfl⟩

/-- The transported inertia subgroup is normal in `Gal(L/Z_w)`. -/
instance inertiaGroupOverDecompositionField_normal
    [FiniteDimensional K L] (A : _root_.ValuationSubring L) :
    (inertiaGroupOverDecompositionField (K := K) A).Normal := by
  let e :=
    decompositionGroupEquivGalDecompositionField_of_finiteDimensional
      (K := K) A
  simpa [inertiaGroupOverDecompositionField, e] using
    (Subgroup.Normal.map (inertiaGroup_normal (K := K) A)
      e.toMonoidHom e.surjective)


















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
    (A : _root_.ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (residueAction K A).range :=
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
