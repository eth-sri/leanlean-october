module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MaximalAbelianKernel

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Infinite abelian class-field correspondence

Maximal abelian reciprocity transports closed subgroups of the idele-class
component quotient to closed subgroups of the maximal abelian Galois group.
Composing this transport with the infinite Galois correspondence gives the
order-reversing infinite abelian class-field correspondence.
-/

open scoped Classical NumberField

noncomputable section

namespace ClosedSubgroup

variable {G H : Type*}
  [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H]

/-- Transport a closed subgroup along a continuous multiplicative
equivalence. -/
noncomputable def mapContinuousMulEquiv
    (e : G ≃ₜ* H) (S : ClosedSubgroup G) : ClosedSubgroup H where
  toSubgroup := e.toMulEquiv.mapSubgroup S.toSubgroup
  isClosed' := by
    change IsClosed (e '' (S : Set G))
    exact e.toHomeomorph.isClosedMap (S : Set G) S.isClosed'

/-- A continuous multiplicative equivalence induces an order equivalence on
closed subgroups. -/
noncomputable def orderIsoMapContinuousMulEquiv
    (e : G ≃ₜ* H) : ClosedSubgroup G ≃o ClosedSubgroup H where
  toFun := mapContinuousMulEquiv e
  invFun := mapContinuousMulEquiv e.symm
  left_inv S := by
    apply ClosedSubgroup.toSubgroup_injective
    change
      e.symm.toMulEquiv.mapSubgroup
          (e.toMulEquiv.mapSubgroup S.toSubgroup) =
        S.toSubgroup
    exact e.toMulEquiv.mapSubgroup.left_inv S.toSubgroup
  right_inv T := by
    apply ClosedSubgroup.toSubgroup_injective
    change
      e.toMulEquiv.mapSubgroup
          (e.symm.toMulEquiv.mapSubgroup T.toSubgroup) =
        T.toSubgroup
    exact e.toMulEquiv.mapSubgroup.right_inv T.toSubgroup
  map_rel_iff' {S T} := by
    change
      e.toMulEquiv.mapSubgroup S.toSubgroup ≤
          e.toMulEquiv.mapSubgroup T.toSubgroup ↔
        S.toSubgroup ≤ T.toSubgroup
    exact e.toMulEquiv.mapSubgroup.le_iff_le

/-- The order-dual form of closed-subgroup transport. -/
noncomputable def orderDualIsoMapContinuousMulEquiv
    (e : G ≃ₜ* H) :
    (ClosedSubgroup G)ᵒᵈ ≃o (ClosedSubgroup H)ᵒᵈ where
  toFun S := OrderDual.toDual
    (mapContinuousMulEquiv e (OrderDual.ofDual S))
  invFun T := OrderDual.toDual
    (mapContinuousMulEquiv e.symm (OrderDual.ofDual T))
  left_inv S := by
    exact congrArg OrderDual.toDual
      ((orderIsoMapContinuousMulEquiv e).left_inv (OrderDual.ofDual S))
  right_inv T := by
    exact congrArg OrderDual.toDual
      ((orderIsoMapContinuousMulEquiv e).right_inv (OrderDual.ofDual T))
  map_rel_iff' {S T} := by
    change
      mapContinuousMulEquiv e (OrderDual.ofDual T) ≤
          mapContinuousMulEquiv e (OrderDual.ofDual S) ↔
        OrderDual.ofDual T ≤ OrderDual.ofDual S
    exact (orderIsoMapContinuousMulEquiv e).le_iff_le










end ClosedSubgroup

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open Reciprocity

variable (K : Type) [Field K] [NumberField K]

/-- The infinite abelian class-field correspondence.  The order dual in the
domain records that larger closed idele-class subgroups correspond to smaller
intermediate fields. -/
noncomputable def infiniteAbelianClassFieldCorrespondence :
    (ClosedSubgroup (ideleClassComponentQuotient K))ᵒᵈ ≃o
      IntermediateField K (maximalAbelianExtension K) :=
  (ClosedSubgroup.orderDualIsoMapContinuousMulEquiv
      (ideleClassComponentQuotientEquivMaximalAbelianGalois K)).trans
    (InfiniteGalois.IntermediateFieldEquivClosedSubgroup
      (k := K) (K := maximalAbelianExtension K)).symm

/-- Forward evaluation is the fixed field of the transported closed
idele-class subgroup. -/
@[simp]
theorem infiniteAbelianClassFieldCorrespondence_apply
    (H : ClosedSubgroup (ideleClassComponentQuotient K)) :
    infiniteAbelianClassFieldCorrespondence K (OrderDual.toDual H) =
      IntermediateField.fixedField
        (ClosedSubgroup.mapContinuousMulEquiv
          (ideleClassComponentQuotientEquivMaximalAbelianGalois K) H) :=
  rfl

/-- The inverse correspondence is the fixing subgroup transported back to
the idele-class component quotient. -/
@[simp]
theorem infiniteAbelianClassFieldCorrespondence_symm_apply
    (L : IntermediateField K (maximalAbelianExtension K)) :
    (infiniteAbelianClassFieldCorrespondence K).symm L =
      OrderDual.toDual
        (ClosedSubgroup.mapContinuousMulEquiv
          (ideleClassComponentQuotientEquivMaximalAbelianGalois K).symm
          { toSubgroup := L.fixingSubgroup
            isClosed' := InfiniteGalois.fixingSubgroup_isClosed L }) :=
  rfl












































end GlobalClassFields
end GlobalClassFieldTheory

end
