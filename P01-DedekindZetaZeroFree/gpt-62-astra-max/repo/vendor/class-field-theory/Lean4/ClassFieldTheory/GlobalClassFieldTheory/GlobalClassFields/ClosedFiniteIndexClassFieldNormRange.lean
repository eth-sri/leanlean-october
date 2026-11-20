module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Norm range over the canonical fixed-field base

This leaf compares the selected abstract norm subgroup with the actual
idèle-class norm range over the canonical fixed-field base.
-/

open scoped Classical IsMulCommutative NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable {K : Type} [Field K] [NumberField K]

/-- Opaque bridge from multiplicative subgroup transport to its additive
presentation.  Keeping this generic prevents concrete fixed-field endpoints
from being unfolded by `rw` while comparing the two presentations. -/
private theorem subgroup_map_toAddSubgroup_mulEquiv
    {G G₂ : Type*} [Group G] [Group G₂]
    (S : Subgroup G) (e : G ≃* G₂) :
    (S.map e.toMonoidHom).toAddSubgroup =
      S.toAddSubgroup.map
        (MulEquiv.toAdditive e).toAddMonoidHom := (MonoidHom.coe_toAdditive_map e.toMonoidHom S).symm

section

variable (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]

/-- The idèle-class transport attached to the selected base equivalence.
Naming this endpoint once keeps the fixed-field instance tower out of
downstream definitional-equality checks. -/
 noncomputable def closedFiniteIndexClassFieldIdeleClassEquiv :
    IdeleClassGroup K ≃*
      IdeleClassGroup
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed) :=
  ideleClassCongr
    (closedFiniteIndexClassFieldBaseEquiv
      (K := K) H hclosed)

/-- Additive form of the selected class-field norm-range computation, with
the concrete idèle-class endpoint hidden behind one typed definition. -/
private theorem closedFiniteIndexClassField_ideleClassNorm_range_toAddSubgroup :
    (_root_.ideleClassNorm
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range.toAddSubgroup =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (closedFiniteIndexClassFieldIdeleClassEquiv
            (K := K) H hclosed)).toAddMonoidHom := by
  simpa only [closedFiniteIndexClassFieldIdeleClassEquiv,
    closedFiniteIndexClassField,
    closedFiniteIndexClassFieldBase,
    closedFiniteIndexClassFieldBaseEquiv] using
    (ordinaryNormClassField_ideleClassNorm_range K
      (closedFiniteIndexClassFieldNormAmbient
        (K := K) H hclosed) H
      (closedFiniteIndexClassFieldNormAmbient_normRange_le
        (K := K) H hclosed))

end

/-- The represented abstract norm subgroup as the same named actual norm
range.  This wrapper uses the lightweight named-field API, avoiding the
dependent `letI` tower in the raw fixed-field comparison theorem. -/
private theorem
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassField_eq_range
    (H : Subgroup (IdeleClassGroup K))
    (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex] :
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      (_root_.ideleClassNorm
        (closedFiniteIndexClassFieldBase
          (K := K) H hclosed)
        (closedFiniteIndexClassField
          (K := K) H hclosed)).range.toAddSubgroup := by
  simpa using
    (ordinaryIdeleClassNormSubgroup_eq_namedNormRange
      (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
         H hclosed)
      (closedFiniteIndexClassFieldSubextension
         H hclosed))

variable (H : Subgroup (IdeleClassGroup K)) (hclosed : IsClosed (H : Set (IdeleClassGroup K)))
    [H.FiniteIndex]

/-- Over the canonical fixed-field base, the determinant-norm range of
the selected class field is the transport of `H`. -/
theorem closedFiniteIndexClassField_ideleClassNorm_range_over_base :
    (_root_.ideleClassNorm
      (closedFiniteIndexClassFieldBase
        (K := K) H hclosed)
      (closedFiniteIndexClassField
        (K := K) H hclosed)).range =
      H.map
        (ideleClassCongr
          (closedFiniteIndexClassFieldBaseEquiv
            (K := K) H hclosed)).toMonoidHom := by
  change
    (_root_.ideleClassNorm
      (closedFiniteIndexClassFieldBase
         H hclosed)
      (closedFiniteIndexClassField
         H hclosed)).range =
      H.map
        (closedFiniteIndexClassFieldIdeleClassEquiv
           H hclosed).toMonoidHom
  apply
    Subgroup.toAddSubgroup.injective
  calc
    (_root_.ideleClassNorm
        (closedFiniteIndexClassFieldBase
           H hclosed)
        (closedFiniteIndexClassField
           H hclosed)).range.toAddSubgroup =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (closedFiniteIndexClassFieldIdeleClassEquiv
               H hclosed)).toAddMonoidHom :=
      closedFiniteIndexClassField_ideleClassNorm_range_toAddSubgroup
         H hclosed
    _ =
        (H.map
          (closedFiniteIndexClassFieldIdeleClassEquiv
             H hclosed).toMonoidHom).toAddSubgroup :=
      (subgroup_map_toAddSubgroup_mulEquiv H
        (closedFiniteIndexClassFieldIdeleClassEquiv
           H hclosed)).symm

/-- The selected subextension is a literal preimage of the transported
closed finite-index subgroup under the ordinary norm-subgroup
correspondence. -/
theorem
    ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassFieldSubextension :
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
          (K := K) H hclosed)
        (closedFiniteIndexClassFieldSubextension
          (K := K) H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (ideleClassCongr
            (closedFiniteIndexClassFieldBaseEquiv
              (K := K) H hclosed))).toAddMonoidHom := by
  change
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
           H hclosed)
        (closedFiniteIndexClassFieldSubextension
           H hclosed) =
      H.toAddSubgroup.map
        (MulEquiv.toAdditive
          (closedFiniteIndexClassFieldIdeleClassEquiv
             H hclosed)).toAddMonoidHom
  calc
    ordinaryIdeleClassNormSubgroup
        (closedFiniteIndexClassFieldReciprocityFiniteAbstractField
           H hclosed)
        (closedFiniteIndexClassFieldSubextension
           H hclosed) =
        (_root_.ideleClassNorm
          (closedFiniteIndexClassFieldBase
             H hclosed)
          (closedFiniteIndexClassField
             H hclosed)).range.toAddSubgroup :=
      ordinaryIdeleClassNormSubgroup_closedFiniteIndexClassField_eq_range
         H hclosed
    _ =
        H.toAddSubgroup.map
          (MulEquiv.toAdditive
            (closedFiniteIndexClassFieldIdeleClassEquiv
               H hclosed)).toAddMonoidHom :=
      closedFiniteIndexClassField_ideleClassNorm_range_toAddSubgroup
         H hclosed
end GlobalClassFields
end GlobalClassFieldTheory

end
