module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.EmbeddedAbelianSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertNormCharacterization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import Mathlib.NumberTheory.NumberField.Basic
public import ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/










set_option autoImplicit false

/-!
# The maximal finite-unramified abelian subextension

The selected big Hilbert class field is characterized here in actual
field order.  Its abstract norm subgroup in the rational absolute
idele-class formation is identified exactly with the intrinsic
big-Hilbert subgroup of its fixed-field base.  Every finite abelian
subextension whose actual fixed-field extension is unramified at all
finite places has a larger norm subgroup, hence lies below the selected
big Hilbert class field by the order-reversing finite classification.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open LocalClassFieldTheory NumberField Reciprocity

 structure BigHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) where
  subgroup : AddSubgroup B
  map_symm : subgroup.map e.symm.toAddMonoidHom = H
  mem_iff (x : B) : x ∈ subgroup ↔ e.symm x ∈ H

 def bigHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) :
    BigHilbertTransportedAddSubgroupData e H where
  subgroup := H.map e.toAddMonoidHom
  map_symm :=
    (AddSubgroup.map_symm_eq_iff_map_eq
      (K := H) (H := H.map e.toAddMonoidHom) (e := e)).2 rfl
  mem_iff := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩



/-- The intrinsic big-Hilbert norm subgroup of an actual rational fixed
field, transported into the rational absolute idele-class formation. -/
noncomputable def bigHilbertNormSubgroupInRationalClassFormation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :=
  (bigHilbertClassFieldNormSubgroup
    (K := abstractFixedField
      ℚ (SeparableClosure ℚ) K.field)).toAddSubgroup.map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K.field).toAddMonoidHom

 

 



/-- The fixed-field idele-class equivalence at the selected big-Hilbert
base, named once so later subgroup comparisons do not reconstruct it. -/
 noncomputable def bigHilbertClassFieldMaximalIdeleClassEquiv
    (K : Type) [Field K] [NumberField K] :
    Additive (IdeleClassGroup (bigHilbertClassFieldBase K)) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K) :=
  rationalAbstractFixedFieldIdeleClassEquivFixed
    (bigHilbertClassFieldBaseSubgroup K)

/-- The intrinsic ordinary norm subgroup at the selected base, with its
additive carrier fixed in the declaration type. -/
 noncomputable def bigHilbertClassFieldMaximalIntrinsicNormSubgroup
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup (Additive (IdeleClassGroup (bigHilbertClassFieldBase K))) :=
  (bigHilbertClassFieldNormSubgroup
    (K := bigHilbertClassFieldBase K)).toAddSubgroup

/-- The selected abstract norm subgroup, with its ambient additive carrier
fixed once in the declaration type. -/
 noncomputable def bigHilbertClassFieldMaximalActualNormEndpoint
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K)) :=
  (bigHilbertClassFieldSubextension K).normSubgroup
    rationalIdeleClassRepresentation

 noncomputable def bigHilbertClassFieldMaximalTransportData
    (K : Type) [Field K] [NumberField K] :
    BigHilbertTransportedAddSubgroupData
      (bigHilbertClassFieldMaximalIdeleClassEquiv K)
      (bigHilbertClassFieldMaximalIntrinsicNormSubgroup K) :=
  bigHilbertTransportedAddSubgroupData
    (bigHilbertClassFieldMaximalIdeleClassEquiv K)
    (bigHilbertClassFieldMaximalIntrinsicNormSubgroup K)

/-- A short typed name for the transported intrinsic subgroup used below. -/
 noncomputable def bigHilbertClassFieldMaximalNormEndpoint
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K)) :=
  (bigHilbertClassFieldMaximalTransportData K).subgroup



private theorem bigHilbertClassFieldMaximalNormEndpoint_mem_iff
    (K : Type) [Field K] [NumberField K]
    (x : ambientFixedAddSubgroup rationalIdeleClassRepresentation
      (bigHilbertClassFieldBaseSubgroup K)) :
    x ∈ bigHilbertClassFieldMaximalNormEndpoint K ↔
      (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm x ∈
        bigHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
  (bigHilbertClassFieldMaximalTransportData K).mem_iff x

private theorem bigHilbertClassFieldMaximalNormEndpoint_eq_public
    (K : Type) [Field K] [NumberField K] :
    bigHilbertClassFieldMaximalNormEndpoint K =
      bigHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (bigHilbertClassFieldNormAmbient K)) := by
  rfl

/-- Mapping the selected abstract norm subgroup back to the ordinary
idele-class group gives the named intrinsic subgroup. -/
private theorem bigHilbertClassFieldMaximalNormSubgroup_map_symm
    (K : Type) [Field K] [NumberField K] :
    (bigHilbertClassFieldMaximalActualNormEndpoint K).map
      (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
        bigHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  let L :=
    bigHilbertClassFieldSubextension K
  let F :=
    bigHilbertClassFieldBase K
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (bigHilbertClassFieldBaseSubgroup K)
  let hLfinite : Finite
      ((bigHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (bigHilbertClassFieldBaseSubgroup K)
          L.field L.below) :=
    L.finite
  calc
    (L.normSubgroup rationalIdeleClassRepresentation).map
        e.symm.toAddMonoidHom =
      (_root_.ideleClassNorm
        F (bigHilbertClassField K)).range.toAddSubgroup := by
      change
        (finiteNormSubgroup rationalIdeleClassRepresentation
            (bigHilbertClassFieldBaseSubgroup K)
            L.field L.below).map
            e.symm.toAddMonoidHom =
          (_root_.ideleClassNorm
            F (bigHilbertClassField K)).range.toAddSubgroup
      simpa only [L, F, e, bigHilbertClassField,
        bigHilbertClassFieldBase,
        bigHilbertClassFieldMaximalIdeleClassEquiv] using
        (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
          (bigHilbertClassFieldBaseSubgroup K)
          (bigHilbertClassFieldSubextension K).field
          (bigHilbertClassFieldSubextension K).below
          (bigHilbertClassFieldSubextension K).normal)
    _ = bigHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
      exact
        congrArg Subgroup.toAddSubgroup
          (bigHilbertClassField_ideleClassNorm_range_eq_intrinsic
            (K := K))

/-- Membership in the selected abstract norm subgroup is detected after
applying the named inverse fixed-field equivalence. -/
private theorem bigHilbertClassFieldMaximalActualNormEndpoint_mem_iff
    (K : Type) [Field K] [NumberField K] :
    ∀ x : ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (bigHilbertClassFieldBaseSubgroup K),
      x ∈ bigHilbertClassFieldMaximalActualNormEndpoint K ↔
        (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm x ∈
          bigHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  intro x
  have hmem :=
    congrArg
      (fun S =>
        (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm x ∈ S)
      (bigHilbertClassFieldMaximalNormSubgroup_map_symm K)
  constructor
  · intro hx
    exact hmem.mp ⟨x, hx, rfl⟩
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hmem.mpr hx
    have hxy : y = x :=
      (bigHilbertClassFieldMaximalIdeleClassEquiv K).symm.injective hyx
    subst y
    exact hy

private theorem bigHilbertClassFieldMaximalNormSubgroup_eq_endpoint
    (K : Type) [Field K] [NumberField K] :
    bigHilbertClassFieldMaximalActualNormEndpoint K =
      bigHilbertClassFieldMaximalNormEndpoint K := by
  apply AddSubgroup.ext
  intro x
  exact
    (bigHilbertClassFieldMaximalActualNormEndpoint_mem_iff K x).trans
      (bigHilbertClassFieldMaximalNormEndpoint_mem_iff K x).symm

/-- The selected big Hilbert class-field subextension realizes exactly
the intrinsic big-Hilbert norm subgroup in the rational absolute class
formation. -/
@[simp]
theorem bigHilbertClassFieldSubextension_normSubgroup
    (K : Type) [Field K] [NumberField K] :
    (bigHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      bigHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (bigHilbertClassFieldNormAmbient K)) := by
  calc
    (bigHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      bigHilbertClassFieldMaximalActualNormEndpoint K := by
        rfl
    _ =
      bigHilbertClassFieldMaximalNormEndpoint K :=
        bigHilbertClassFieldMaximalNormSubgroup_eq_endpoint K
    _ = bigHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (bigHilbertClassFieldNormAmbient K)) :=
      bigHilbertClassFieldMaximalNormEndpoint_eq_public K

section GeneralFixedFieldContainment

variable
    (K₀ : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (P₀ : FiniteAbelianSubextension K₀.field)

local instance maximalSubextensionBaseQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K₀.field (le_baseField K₀.field)) :=
  K₀.finite

local instance maximalSubextensionRelativeQuotientFinite :
    Finite
      (K₀.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K₀.field P₀.field P₀.below) :=
  P₀.finite

noncomputable local instance maximalSubextensionBaseFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K₀.field K₀.finite

noncomputable local instance maximalSubextensionRelativeFiniteDimensional :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K₀.field P₀.field P₀.below K₀.finite P₀.finite

local instance maximalSubextensionRelativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance maximalSubextensionTopFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P₀.below)

noncomputable local instance maximalSubextensionBaseNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)

noncomputable local instance maximalSubextensionTopNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P₀.below)

noncomputable local instance maximalSubextensionRelativeIsGalois :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K₀.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P₀.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K₀.field P₀.field P₀.below P₀.normal







end GeneralFixedFieldContainment



section FixedFieldMaximalityInstances

variable
    (K : Type) [Field K] [NumberField K]
    (P : FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K))

local instance bigHilbertMaximalRelativeQuotientFinite :
    Finite
      ((bigHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (bigHilbertClassFieldBaseSubgroup K)
          P.field P.below) :=
  P.finite

noncomputable local instance bigHilbertMaximalRelativeFiniteDimensional :
    FiniteDimensional
      (bigHilbertClassFieldBase K)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (bigHilbertClassFieldBaseSubgroup K)
    P.field P.below inferInstance P.finite

local instance bigHilbertMaximalRelativeScalarTower :
    IsScalarTower ℚ
      (bigHilbertClassFieldBase K)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance bigHilbertMaximalTopFiniteDimensional :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  FiniteDimensional.trans ℚ
    (bigHilbertClassFieldBase K)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance bigHilbertMaximalTopNumberField :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below)

noncomputable local instance bigHilbertMaximalRelativeIsGalois :
    IsGalois
      (bigHilbertClassFieldBase K)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (bigHilbertClassFieldBaseSubgroup K)
    P.field P.below P.normal



end FixedFieldMaximalityInstances



/-!
## Maximality over the original number field

The preceding order statement lives over the fixed-field copy of the
base used by the rational absolute class formation.  We now embed an
arbitrary actual finite abelian extension `E / K` compatibly with that
copy, apply the fixed-field maximality theorem there, and restrict its
ambient embedding to the selected big Hilbert class field.
-/

/-- The distinguished embedding of the original number field into the
rational separable closure underlying the selected big Hilbert class
field. -/
noncomputable def bigHilbertClassFieldBaseEmbedding
    (K : Type) [Field K] [NumberField K] :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  numberFieldTowerLowerEmbedding K
    (bigHilbertClassFieldNormAmbient K)

/-- The canonical fixed-field equivalence has the distinguished base
embedding as its underlying map into the rational separable closure. -/
@[simp]
theorem bigHilbertClassFieldBaseEquiv_coe
    (K : Type) [Field K] [NumberField K]
    (x : K) :
    ((bigHilbertClassFieldBaseEquiv (K := K) x :
        bigHilbertClassFieldBase K) :
      SeparableClosure ℚ) =
      bigHilbertClassFieldBaseEmbedding K x := by
  rfl

/-- An actual finite extension of `K`, embedded into the rational
separable closure so that its restriction to `K` is exactly the base
embedding used by the selected big Hilbert class field. -/
noncomputable def bigHilbertClassFieldCompatibleEmbedding
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    E →ₐ[ℚ] SeparableClosure ℚ :=
  Classical.choose
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (bigHilbertClassFieldBaseEmbedding K))

/-- Compatibility of the chosen ambient embedding with the selected
copy of the original base field. -/
@[simp]
theorem bigHilbertClassFieldCompatibleEmbedding_restrictDomain
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    (bigHilbertClassFieldCompatibleEmbedding K E).domRestrict K =
      bigHilbertClassFieldBaseEmbedding K :=
  Classical.choose_spec
    (IsAlgClosed.surjective_domRestrict_of_isAlgebraic
      (K := ℚ) (L := K) (E := E)
      (M := SeparableClosure ℚ)
      (bigHilbertClassFieldBaseEmbedding K))

/-- Evaluation on the original scalar map agrees with the distinguished
base embedding. -/
@[simp]
theorem bigHilbertClassFieldCompatibleEmbedding_algebraMap
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (x : K) :
    bigHilbertClassFieldCompatibleEmbedding K E
        (algebraMap K E x) =
      bigHilbertClassFieldBaseEmbedding K x := by
  have h :=
    DFunLike.congr_fun
      (bigHilbertClassFieldCompatibleEmbedding_restrictDomain K E) x
  exact h

/-- The fixing subgroup of the compatible embedded copy of `K` is the
base subgroup of the selected big Hilbert class field. -/
@[simp]
theorem bigHilbertClassFieldCompatibleEmbedding_baseSubgroup
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] :
    numberFieldEmbeddedBaseSubgroup K E
        (bigHilbertClassFieldCompatibleEmbedding K E) =
      bigHilbertClassFieldBaseSubgroup K := by
  change
    RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        ((bigHilbertClassFieldCompatibleEmbedding K E).domRestrict K).fieldRange =
      RamificationTheory.closedFixingSubgroup ℚ (SeparableClosure ℚ)
        (bigHilbertClassFieldBaseEmbedding K).fieldRange
  exact
    congrArg
      (fun i : K →ₐ[ℚ] SeparableClosure ℚ =>
        RamificationTheory.closedFixingSubgroup ℚ
          (SeparableClosure ℚ) i.fieldRange)
      (bigHilbertClassFieldCompatibleEmbedding_restrictDomain K E)

/-- The actual finite abelian extension `E / K`, represented inside the
same rational absolute Galois group as the selected big Hilbert class
field. -/
noncomputable def bigHilbertClassFieldEmbeddedAbelianSubextension
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    FiniteAbelianSubextension
      (bigHilbertClassFieldBaseSubgroup K) :=
  numberFieldEmbeddedAbelianSubextension K E
    (bigHilbertClassFieldCompatibleEmbedding K E)
    (bigHilbertClassFieldBaseSubgroup K)
    (bigHilbertClassFieldCompatibleEmbedding_baseSubgroup K E)

/-- The top subgroup of the embedded abelian subextension is exactly
the fixing subgroup of the compatible embedded copy of `E`. -/
@[simp]
theorem bigHilbertClassFieldEmbeddedAbelianSubextension_field
    (K E : Type)
    [Field K] [NumberField K]
    [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    (bigHilbertClassFieldEmbeddedAbelianSubextension K E).field =
      numberFieldEmbeddedTopSubgroup K E
        (bigHilbertClassFieldCompatibleEmbedding K E) := by
  exact
    numberFieldEmbeddedAbelianSubextension_field K E
      (bigHilbertClassFieldCompatibleEmbedding K E)
      (bigHilbertClassFieldBaseSubgroup K)
      (bigHilbertClassFieldCompatibleEmbedding_baseSubgroup K E)









end GlobalClassFields
end GlobalClassFieldTheory

end
