module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassNormTopology

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Class fields from ordinary idele-class norm neighbourhoods

An actual finite Galois norm subgroup contained in an ordinary
idele-class subgroup makes the transported subgroup norm-open in the
rational absolute class formation.  Finite abelian classification then
constructs its class field.  The final theorem below transports the
result back to the ordinary idele class group of the actual fixed field,
so its conclusion is an equality of genuine determinant-norm ranges.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity

/-- Fix the canonical quotient group before converting fixed-field
equivalences to additive homomorphisms. -/
@[instance_reducible]
 noncomputable def ordinaryNormClassFieldIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] ordinaryNormClassFieldIdeleClassCommGroup

private theorem addSubgroup_map_map_eq_of_comp_eq
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (S : AddSubgroup A) (f : A →+ B) (g : B →+ C) (h : A →+ C)
    (hcomp : g.comp f = h) :
    (S.map f).map g = S.map h := by
  rw [AddSubgroup.map_map, hcomp]

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/- The fixed-field typeclass data used by the topology comparison are kept
behind named constants.  This prevents every consumer from rebuilding the
same finite-dimensional and number-field proof terms while reducing the
dependent fixed-field type. -/
omit [FiniteDimensional K L] [IsGalois K L] in
 theorem numberFieldTowerFixedBaseFiniteDimensionalPackage :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)

omit [FiniteDimensional K L] [IsGalois K L] in
 theorem numberFieldTowerFixedBaseNumberFieldPackage :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) := by
  exact
    NumberField.of_module_finite ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L))

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable local instance
    numberFieldTowerFixedBaseFiniteDimensional :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  numberFieldTowerFixedBaseFiniteDimensionalPackage K L

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable local instance numberFieldTowerFixedBaseNumberField :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ)
        (numberFieldTowerBaseSubgroup K L)) :=
  numberFieldTowerFixedBaseNumberFieldPackage K L

/- The norm-open subgroup and its openness proof form one opaque value.  Both
the classification theorem and the topology comparison consume projections
of this same package. -/
 noncomputable def ordinaryNormOpenSubgroup
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    ClassFormation.FiniteAbelianSubextension.NormOpenAddSubgroup
      rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L) := by
  refine ⟨H.toAddSubgroup.map ((numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom), ?_⟩
  exact numberFieldTowerTransport_isNormOpen_of_normRange_le K L H hLH

section FixedBaseTransport

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerIdeleClassEquivAmbientFixed_symm_apply
    (c : Additive (IdeleClassGroup K)) :
    (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm
      (numberFieldTowerIdeleClassEquivAmbientFixed K L c) =
        MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv K L)) c := by
  simpa only [numberFieldTowerIdeleClassEquivAmbientFixed,
    AddEquiv.trans_apply] using
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm_apply_apply ((MulEquiv.toAdditive
        (ideleClassCongr
          (numberFieldTowerAbstractBaseFieldEquiv K L))) c)

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem numberFieldTowerIdeleClassEquivAmbientFixed_comp :
    (rationalAbstractFixedFieldIdeleClassEquivFixed
        (numberFieldTowerBaseSubgroup K L)).symm.toAddMonoidHom.comp
      (numberFieldTowerIdeleClassEquivAmbientFixed K L).toAddMonoidHom =
        (MulEquiv.toAdditive
          (ideleClassCongr
            (numberFieldTowerAbstractBaseFieldEquiv K L))) := by
  apply AddMonoidHom.ext
  intro c
  exact
    numberFieldTowerIdeleClassEquivAmbientFixed_symm_apply
      K L c

end FixedBaseTransport

section

variable (H : Subgroup (IdeleClassGroup K)) (hLH : (_root_.ideleClassNorm K L).range ≤ H)

include hLH in
/-- A finite Galois norm neighbourhood inside an ordinary idele-class
subgroup produces a finite abelian subextension whose abstract norm
subgroup is exactly the transported ordinary subgroup. -/
theorem exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le :
    ∃ M : FiniteAbelianSubextension
        (numberFieldTowerBaseSubgroup K L),
      M.normSubgroup rationalIdeleClassRepresentation =
        (H.toAddSubgroup).map
          (numberFieldTowerIdeleClassEquivAmbientFixed
            K L).toAddMonoidHom := by
  let :=
    numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L
  let B : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
    { field := numberFieldTowerBaseSubgroup K L
      finite := numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L }
  let N := ordinaryNormOpenSubgroup K L H hLH
  obtain ⟨M, hM⟩ :
      ∃ M : FiniteAbelianSubextension
          (numberFieldTowerBaseSubgroup K L),
        FiniteAbelianSubextension.normSubgroupMap
            rationalIdeleClassRepresentation M = N :=
    FiniteAbelianSubextension.normSubgroupMap_surjective
      Reciprocity.rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom B N
  refine ⟨M, ?_⟩
  rw [← FiniteAbelianSubextension.normSubgroupMap_val]
  rw [congrArg Subtype.val hM]
  exact rfl

/-- The finite abelian subextension selected from an ordinary norm
neighbourhood.  This is the unique choice point for the realization API
below. -/
noncomputable def ordinaryNormClassFieldSubextension :
    FiniteAbelianSubextension (numberFieldTowerBaseSubgroup K L) :=
  Classical.choose
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

/-- The selected subextension has the prescribed abstract norm subgroup. -/
theorem ordinaryNormClassFieldSubextension_normSubgroup :
    (ordinaryNormClassFieldSubextension K L H hLH).normSubgroup
        rationalIdeleClassRepresentation =
      H.toAddSubgroup.map
        (numberFieldTowerIdeleClassEquivAmbientFixed
          K L).toAddMonoidHom :=
  Classical.choose_spec
    (exists_finiteAbelianSubextension_normSubgroup_eq_of_normRange_le
      K L H hLH)

end

/-- The canonical fixed-field copy of the base used by every ordinary
norm-neighbourhood realization in the ambient extension `L / K`. -/
noncomputable abbrev ordinaryNormClassFieldBase : Type :=
  abstractFixedField ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable instance ordinaryNormClassFieldBaseFiniteDimensional :
    FiniteDimensional ℚ (ordinaryNormClassFieldBase K L) :=
  numberFieldTowerFixedBaseFiniteDimensionalPackage K L

omit [FiniteDimensional K L] [IsGalois K L] in
noncomputable instance ordinaryNormClassFieldBaseNumberField :
    NumberField (ordinaryNormClassFieldBase K L) :=
  numberFieldTowerFixedBaseNumberFieldPackage K L

/-- The actual relative fixed field of the selected ordinary class-field
subextension. -/
noncomputable abbrev ordinaryNormClassFieldExtension
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) : Type :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (ordinaryNormClassFieldSubextension K L H hLH).below

noncomputable instance ordinaryNormClassFieldExtensionFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (numberFieldTowerBaseSubgroupAbsoluteQuotientFinite K L)
    (ordinaryNormClassFieldSubextension K L H hLH).finite

noncomputable instance ordinaryNormClassFieldScalarTower
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsScalarTower ℚ (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable instance ordinaryNormClassFieldAbsoluteFiniteDimensional
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    FiniteDimensional ℚ
      (ordinaryNormClassFieldExtension K L H hLH) :=
  FiniteDimensional.trans ℚ (ordinaryNormClassFieldBase K L)
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionNumberField
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    NumberField (ordinaryNormClassFieldExtension K L H hLH) :=
  NumberField.of_module_finite ℚ
    (ordinaryNormClassFieldExtension K L H hLH)

noncomputable instance ordinaryNormClassFieldExtensionIsGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    (numberFieldTowerBaseSubgroup K L)
    (ordinaryNormClassFieldSubextension K L H hLH).field
    (ordinaryNormClassFieldSubextension K L H hLH).below
    (ordinaryNormClassFieldSubextension K L H hLH).normal

noncomputable instance ordinaryNormClassFieldExtensionIsAbelianGalois
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    IsAbelianGalois (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (ordinaryNormClassFieldSubextension K L H hLH)

/-- The canonical equivalence from the original base to the selected
fixed-field base. -/
noncomputable abbrev ordinaryNormClassFieldBaseEquiv :
    K ≃ₐ[ℚ] ordinaryNormClassFieldBase K L :=
  numberFieldTowerAbstractBaseFieldEquiv K L

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem ordinaryNormClassFieldBaseIdeleClassTransport_comp :
    let B := numberFieldTowerBaseSubgroup K L
    let eFixed := rationalAbstractFixedFieldIdeleClassEquivFixed B
    let eBase :=
      MulEquiv.toAdditive
        (ideleClassCongr (ordinaryNormClassFieldBaseEquiv K L))
    let eTower := numberFieldTowerIdeleClassEquivAmbientFixed K L
    eFixed.symm.toAddMonoidHom.comp eTower.toAddMonoidHom =
      eBase.toAddMonoidHom := numberFieldTowerIdeleClassEquivAmbientFixed_comp K L

/-- The determinant-norm range of the selected ordinary class field is
the original subgroup transported to the canonical fixed-field base. -/
theorem ordinaryNormClassField_ideleClassNorm_range
    (H : Subgroup (IdeleClassGroup K))
    (hLH : (_root_.ideleClassNorm K L).range ≤ H) :
    (_root_.ideleClassNorm
      (ordinaryNormClassFieldBase K L)
      (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (ideleClassCongr
              (ordinaryNormClassFieldBaseEquiv K L))).toAddMonoidHom := by
  let M := ordinaryNormClassFieldSubextension K L H hLH
  let B := numberFieldTowerBaseSubgroup K L
  let hRelativeQuotientFinite :=
    M.finite
  let eFixed := rationalAbstractFixedFieldIdeleClassEquivFixed B
  let eTower := numberFieldTowerIdeleClassEquivAmbientFixed K L
  let f : Additive (IdeleClassGroup K) →+
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation B :=
    eTower.toAddMonoidHom
  let Additive₀ := Additive (IdeleClassGroup (ordinaryNormClassFieldBase K L))
  let g : KummerTheory.ambientFixedAddSubgroup
      rationalIdeleClassRepresentation B →+
        Additive₀ :=
    eFixed.symm.toAddMonoidHom
  let h : Additive (IdeleClassGroup K) →+
      Additive₀ :=
    (MulEquiv.toAdditive
      (ideleClassCongr
        (ordinaryNormClassFieldBaseEquiv K L))).toAddMonoidHom
  have hnorm :
      (M.normSubgroup rationalIdeleClassRepresentation).map
          g =
        (_root_.ideleClassNorm
          (ordinaryNormClassFieldBase K L)
          (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup := by
    simpa only [FiniteAbelianSubextension.normSubgroup,
      M, B, ordinaryNormClassFieldBase,
      ordinaryNormClassFieldExtension] using
      (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
        B M.field M.below M.normal)
  have hcomp :
      g.comp f = h := by
    simpa only [f, g, h, eFixed, eTower] using
      (ordinaryNormClassFieldBaseIdeleClassTransport_comp K L)
  calc
    (_root_.ideleClassNorm
          (ordinaryNormClassFieldBase K L)
          (ordinaryNormClassFieldExtension K L H hLH)).range.toAddSubgroup =
        (M.normSubgroup rationalIdeleClassRepresentation).map
          g := hnorm.symm
    _ =
        (H.toAddSubgroup.map f).map g := by
      exact
        congrArg
          (fun S : AddSubgroup
              (KummerTheory.ambientFixedAddSubgroup
                rationalIdeleClassRepresentation B) =>
            AddSubgroup.map
              (N := Additive₀) g S)
          (ordinaryNormClassFieldSubextension_normSubgroup
            K L H hLH)
    _ = H.toAddSubgroup.map h := by
      exact
        addSubgroup_map_map_eq_of_comp_eq
          (A := Additive (IdeleClassGroup K))
          (B := KummerTheory.ambientFixedAddSubgroup
            rationalIdeleClassRepresentation B)
          (C := Additive₀)
          (S := H.toAddSubgroup)
          (f := f) (g := g) (h := h)
          (hcomp := hcomp)

end GlobalClassFields
end GlobalClassFieldTheory

end
