module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.HilbertClassFieldUnramifiedMaximality
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerConjugation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# The maximal everywhere-unramified abelian subextension

The selected small Hilbert class field is characterized in actual field
order.  Its rational absolute class-formation norm subgroup is exactly
the intrinsic small-Hilbert subgroup of its fixed-field base.  The
order-reversing finite abelian classification then places every actual
finite abelian extension unramified at all finite and infinite places
inside the selected field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation KummerTheory
open IdealClassFieldTheory LocalClassFieldTheory NumberField Reciprocity

/-- Fix the canonical quotient structure at the boundary between ordinary
idele classes and additive fixed subgroups. -/
@[instance_reducible]
 noncomputable def smallHilbertMaximalSubextensionIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] smallHilbertMaximalSubextensionIdeleClassCommGroup

 structure SmallHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) where
  subgroup : AddSubgroup B
  map_symm : subgroup.map e.symm.toAddMonoidHom = H

 def smallHilbertTransportedAddSubgroupData
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H : AddSubgroup A) :
    SmallHilbertTransportedAddSubgroupData e H where
  subgroup := H.map e.toAddMonoidHom
  map_symm :=
    (AddSubgroup.map_symm_eq_iff_map_eq
      (K := H) (H := H.map e.toAddMonoidHom) (e := e)).2 rfl

private theorem smallHilbertAddSubgroup_eq_of_map_symm_eq
    {A B : Type} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (H J : AddSubgroup B)
    (h : H.map e.symm.toAddMonoidHom =
      J.map e.symm.toAddMonoidHom) :
    H = J := by
  exact AddSubgroup.map_injective e.symm.injective h

/-- The fixed-field idèle-class equivalence at the selected small-Hilbert
base, named once so later subgroup comparisons do not reconstruct it. -/
 noncomputable def smallHilbertClassFieldMaximalIdeleClassEquiv
    (K : Type) [Field K] [NumberField K] :
    Additive (IdeleClassGroup (smallHilbertClassFieldBase K)) ≃+
      ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (smallHilbertClassFieldBaseSubgroup K) :=
  rationalAbstractFixedFieldIdeleClassEquivFixed
    (smallHilbertClassFieldBaseSubgroup K)

/-- The intrinsic ordinary norm subgroup at the selected base, with its
additive carrier fixed in the declaration type. -/
 noncomputable def smallHilbertClassFieldMaximalIntrinsicNormSubgroup
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup (Additive (IdeleClassGroup (smallHilbertClassFieldBase K))) :=
  (smallHilbertClassFieldNormSubgroup
    (K := smallHilbertClassFieldBase K)).toAddSubgroup

 noncomputable def smallHilbertClassFieldMaximalTransportData
    (K : Type) [Field K] [NumberField K] :
    SmallHilbertTransportedAddSubgroupData
      (smallHilbertClassFieldMaximalIdeleClassEquiv K)
      (smallHilbertClassFieldMaximalIntrinsicNormSubgroup K) :=
  smallHilbertTransportedAddSubgroupData
    (smallHilbertClassFieldMaximalIdeleClassEquiv K)
    (smallHilbertClassFieldMaximalIntrinsicNormSubgroup K)

/-- A short typed name for the transported intrinsic subgroup used below.
Keeping this endpoint opaque prevents the fixed-field aliases from being
re-elaborated when the inverse transport is applied. -/
 noncomputable def smallHilbertClassFieldMaximalNormEndpoint
    (K : Type) [Field K] [NumberField K] :
    AddSubgroup
      (ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (smallHilbertClassFieldBaseSubgroup K)) :=
  (smallHilbertClassFieldMaximalTransportData K).subgroup

private theorem smallHilbertClassFieldMaximalNormEndpoint_map_symm
    (K : Type) [Field K] [NumberField K] :
    (smallHilbertClassFieldMaximalNormEndpoint K).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      smallHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
  (smallHilbertClassFieldMaximalTransportData K).map_symm

private theorem smallHilbertClassFieldMaximalNormEndpoint_eq_public
    (K : Type) [Field K] [NumberField K] :
    smallHilbertClassFieldMaximalNormEndpoint K =
      smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) := by
  rfl

/-- Mapping the selected abstract norm subgroup back to the ordinary
idèle-class group gives the named intrinsic subgroup. -/
private theorem smallHilbertClassFieldMaximalNormSubgroup_map_symm
    (K : Type) [Field K] [NumberField K] :
    ((smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation).map
      (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
        smallHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
  let L :=
    smallHilbertClassFieldSubextension K
  let F :=
    smallHilbertClassFieldBase K
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed
      (smallHilbertClassFieldBaseSubgroup K)
  let hLfinite : Finite
      ((smallHilbertClassFieldBaseSubgroup K).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (smallHilbertClassFieldBaseSubgroup K)
          L.field L.below) :=
    L.finite
  calc
    (L.normSubgroup rationalIdeleClassRepresentation).map
        e.symm.toAddMonoidHom =
      (_root_.ideleClassNorm
        F (smallHilbertClassField K)).range.toAddSubgroup := by
      change
        (finiteNormSubgroup rationalIdeleClassRepresentation
            (smallHilbertClassFieldBaseSubgroup K)
            L.field L.below).map
            e.symm.toAddMonoidHom =
          (_root_.ideleClassNorm
            F (smallHilbertClassField K)).range.toAddSubgroup
      simpa only [L, F, e, smallHilbertClassField,
        smallHilbertClassFieldBase,
        smallHilbertClassFieldMaximalIdeleClassEquiv] using
        (map_rationalFiniteNormSubgroup_eq_ordinaryIdeleClassNormRange_concrete
          (smallHilbertClassFieldBaseSubgroup K)
          (smallHilbertClassFieldSubextension K).field
          (smallHilbertClassFieldSubextension K).below
          (smallHilbertClassFieldSubextension K).normal)
    _ = smallHilbertClassFieldMaximalIntrinsicNormSubgroup K := by
      exact
        congrArg Subgroup.toAddSubgroup
          (smallHilbertClassField_ideleClassNorm_range_eq_intrinsic
            (K := K))

/-- Both subgroups have the same inverse image under the fixed-field
idèle-class equivalence. -/
private theorem smallHilbertClassFieldMaximalNormSubgroup_map_eq_endpoint_map
    (K : Type) [Field K] [NumberField K] :
    ((smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation).map
      (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      (smallHilbertClassFieldMaximalNormEndpoint K).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom := by
  calc
    ((smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom =
      smallHilbertClassFieldMaximalIntrinsicNormSubgroup K :=
        smallHilbertClassFieldMaximalNormSubgroup_map_symm K
    _ = (smallHilbertClassFieldMaximalNormEndpoint K).map
        (smallHilbertClassFieldMaximalIdeleClassEquiv K).symm.toAddMonoidHom :=
      (smallHilbertClassFieldMaximalNormEndpoint_map_symm K).symm

private theorem smallHilbertClassFieldMaximalNormSubgroup_eq_endpoint
    (K : Type) [Field K] [NumberField K] :
    (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertClassFieldMaximalNormEndpoint K := by
  exact
    smallHilbertAddSubgroup_eq_of_map_symm_eq
      (A := Additive (IdeleClassGroup (smallHilbertClassFieldBase K)))
      (B := ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (smallHilbertClassFieldBaseSubgroup K))
      (e := smallHilbertClassFieldMaximalIdeleClassEquiv K)
      (H := (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation)
      (J := smallHilbertClassFieldMaximalNormEndpoint K)
      (h := smallHilbertClassFieldMaximalNormSubgroup_map_eq_endpoint_map K)

/-- The selected small Hilbert class-field subextension realizes exactly
the intrinsic small-Hilbert norm subgroup in the rational absolute class
formation. -/
@[simp]
theorem smallHilbertClassFieldSubextension_normSubgroup
    (K : Type) [Field K] [NumberField K] :
    (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) := by
  calc
    (smallHilbertClassFieldSubextension K).normSubgroup
        rationalIdeleClassRepresentation =
      smallHilbertClassFieldMaximalNormEndpoint K :=
        smallHilbertClassFieldMaximalNormSubgroup_eq_endpoint K
    _ = smallHilbertNormSubgroupInRationalClassFormation
        (numberFieldTowerFiniteAbstractField K
          (smallHilbertClassFieldNormAmbient K)) :=
      smallHilbertClassFieldMaximalNormEndpoint_eq_public K









end GlobalClassFields
end GlobalClassFieldTheory

end
