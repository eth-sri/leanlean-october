module

public import ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTower
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/











set_option autoImplicit false

/-!
# Conjugation of the small Hilbert class-field tower

For a finite abelian tower, conjugation by the lower base carries the
relative norm subgroup of the upper extension to the relative norm subgroup
of the conjugate extension.  In the rational absolute idele-class formation,
the subgroup defining the small Hilbert class field is intrinsic under the
corresponding automorphism of its actual fixed field.  Finite abelian
classification therefore identifies every conjugate of the second small
Hilbert class field with the original field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation KummerTheory
open GlobalClassFields LocalClassFieldTheory Reciprocity

private theorem addSubgroup_map_map_eq_of_comp_eq
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (S : AddSubgroup A) (f : A →+ B) (g : B →+ C) (h : A →+ C)
    (hcomp : g.comp f = h) :
    (S.map f).map g = S.map h := by
  rw [AddSubgroup.map_map, hcomp]









section AbstractConjugation

variable
    {G : IntegralRepGroupType}
    [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- A finite Galois field in an abelian tower is stable under conjugation
by every element of its base subgroup. -/
theorem conjugateFiniteAbelianSubextensionField_eq_self
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (s : K.toSubgroup) :
    conjugateClosedSubgroup L.field s.1 = L.field := by
  ext x
  constructor
  · intro hx
    have hx' : s.1 * x * s.1⁻¹ ∈ L.field :=
      (conjugateClosedSubgroup_mem L.field s.1 x).1 hx
    let y : L.field.toSubgroup :=
      ⟨s.1 * x * s.1⁻¹, hx'⟩
    let yK : K.toSubgroup :=
      Subgroup.inclusion L.below y
    have hy :
        s⁻¹ * yK * s ∈
          CyclicCohomology.extensionSubgroup K L.field L.below := by
      simpa only [inv_inv] using
        L.normal.conj_mem yK
          ((mem_extensionSubgroup_iff
            K L.field L.below yK).2 y.2) s⁻¹
    have hyL :
        ((s⁻¹ * yK * s : K.toSubgroup) : G) ∈
          L.field.toSubgroup :=
      (mem_extensionSubgroup_iff K L.field L.below
        (s⁻¹ * yK * s)).1 hy
    change x ∈ L.field.toSubgroup
    simpa [y, yK, mul_assoc] using hyL
  · intro hx
    let xK : K.toSubgroup :=
      ⟨x, L.below hx⟩
    have hxConj :
        s * xK * s⁻¹ ∈
          CyclicCohomology.extensionSubgroup K L.field L.below := by
      exact
        L.normal.conj_mem xK
          ((mem_extensionSubgroup_iff
            K L.field L.below xK).2 hx) s
    apply (conjugateClosedSubgroup_mem L.field s.1 x).2
    simpa [xK] using
      (mem_extensionSubgroup_iff K L.field L.below
        (s * xK * s⁻¹)).1 hxConj





 noncomputable def rebaseFiniteAbelianSubextension
    {K K' : ClosedSubgroup G} (h : K = K')
    (L : FiniteAbelianSubextension K) :
    FiniteAbelianSubextension K' :=
  h ▸ L

omit [ContinuousMul G] in
@[simp]
private theorem rebaseFiniteAbelianSubextension_field
    {K K' : ClosedSubgroup G} (h : K = K')
    (L : FiniteAbelianSubextension K) :
    (rebaseFiniteAbelianSubextension h L).field = L.field := by
  cases h
  rfl

 noncomputable def rebaseFixedCodomainHom
    (A : Rep ℤ G)
    {X : Type*} [AddGroup X]
    {K K' : ClosedSubgroup G} (h : K = K')
    (f : X →+ ambientFixedAddSubgroup A K) :
    X →+
      ambientFixedAddSubgroup A K' := by
  cases h
  exact f

omit [ContinuousMul G] in
@[simp]
private theorem rebaseFixedCodomainHom_coe
    (A : Rep ℤ G)
    {X : Type*} [AddGroup X]
    {K K' : ClosedSubgroup G} (h : K = K')
    (f : X →+ ambientFixedAddSubgroup A K)
    (a : X) :
    ((rebaseFixedCodomainHom A h f a :
      ambientFixedAddSubgroup A K') : A.V) =
      (f a : A.V) := by
  cases h
  rfl

 





/-- Conjugation of the upper extension, transported back across the
conjugation-stability equality of its abelian base. -/
noncomputable def conjugateFiniteAbelianSubextensionOverBase
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (s : K.toSubgroup) :
    FiniteAbelianSubextension L.field :=
  rebaseFiniteAbelianSubextension
    (conjugateFiniteAbelianSubextensionField_eq_self L s)
    (conjugateFiniteAbelianSubextension M s.1)

@[simp]
theorem conjugateFiniteAbelianSubextensionOverBase_field
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (s : K.toSubgroup) :
    (conjugateFiniteAbelianSubextensionOverBase L M s).field =
      conjugateClosedSubgroup M.field s.1 :=
  by
    simp only [
      conjugateFiniteAbelianSubextensionOverBase,
      rebaseFiniteAbelianSubextension_field,
      conjugateFiniteAbelianSubextension_field]

/-- The canonical conjugation map on the fixed part, transported along
the conjugation-stability equality of the abelian base. -/
noncomputable def stableBaseConjugationHom
    (A : Rep ℤ G)
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (s : K.toSubgroup) :
    ambientFixedAddSubgroup A L.field →+
      ambientFixedAddSubgroup A L.field :=
  rebaseFixedCodomainHom A
    (conjugateFiniteAbelianSubextensionField_eq_self L s)
    (conjugateFixedElementHom A L.field s.1)

@[simp]
theorem stableBaseConjugationHom_coe
    (A : Rep ℤ G)
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (s : K.toSubgroup)
    (a : ambientFixedAddSubgroup A L.field) :
    ((stableBaseConjugationHom A L s a :
      ambientFixedAddSubgroup A L.field) : A.V) =
      A.ρ s.1⁻¹ a.1 := by
  calc
    ((stableBaseConjugationHom A L s a :
      ambientFixedAddSubgroup A L.field) : A.V) =
        ((conjugateFixedElementHom A L.field s.1 a :
          ambientFixedAddSubgroup A
            (conjugateClosedSubgroup L.field s.1)) : A.V) := by
      exact rebaseFixedCodomainHom_coe A
        (conjugateFiniteAbelianSubextensionField_eq_self L s)
        (conjugateFixedElementHom A L.field s.1) a
    _ = A.ρ s.1⁻¹ a.1 :=
      conjugateFixedElement_coe A L.field s.1 a



end AbstractConjugation

section RationalSmallHilbert

local instance smallHilbertTowerBaseQuotientFinite
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

local instance smallHilbertTowerRelativeQuotientFinite
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K.field L.field L.below) :=
  L.finite

noncomputable local instance smallHilbertTowerBaseFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance smallHilbertTowerRelativeFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

local instance smallHilbertTowerScalarTower
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance smallHilbertTowerAbsoluteFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance smallHilbertTowerBaseNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

noncomputable local instance smallHilbertTowerRelativeNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance smallHilbertTowerRelativeIsGalois
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal

/-- The ordinary small-Hilbert norm subgroup of an actual fixed field,
transported into the fixed part of the rational absolute idele-class
representation. -/
noncomputable def smallHilbertNormSubgroupInRationalClassFormation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :=
  (smallHilbertClassFieldNormSubgroup
    (K := abstractFixedField
      ℚ (SeparableClosure ℚ) K.field)).toAddSubgroup.map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K.field).toAddMonoidHom

































end RationalSmallHilbert

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
