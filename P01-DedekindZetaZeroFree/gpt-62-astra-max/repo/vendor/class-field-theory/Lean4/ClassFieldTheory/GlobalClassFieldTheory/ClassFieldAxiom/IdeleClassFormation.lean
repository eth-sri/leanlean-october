module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The rational idele-class formation

This module identifies the fixed-field idele-class representation with
concrete relative idele class groups and transfers the cyclic low-degree Tate
cohomology calculation to prove the abstract class-field axiom.
-/

namespace GlobalClassFieldTheory

open scoped NumberField TensorProduct
open NumberField
open CyclicCohomology ClassFormation
open LocalClassFieldTheory

noncomputable section

open CategoryTheory

namespace Reciprocity

/-- The rational absolute idele-class representation satisfies the
abstract class-field axiom. -/
theorem rationalIdeleClassRepresentation_satisfiesClassFieldAxiom :
    SatisfiesClassFieldAxiom rationalIdeleClassRepresentation := by
  rintro ⟨K, hKfinite⟩
  rintro ⟨L, hLK, hnormal, hfinite, g, hg⟩
  let := hKfinite
  let := hnormal
  let := hfinite
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let := Fintype.ofFinite Q
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let :=
    FiniteDimensional.trans ℚ F E
  let := NumberField.of_module_finite ℚ F
  let := NumberField.of_module_finite ℚ E
  let :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let g' := eQ g
  have hg' :=
    map_cyclicGenerator eQ g hg
  let :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  have hIdeleClassTateCard :=
    ClassFieldAxiom.ideleClass_tate_lowDegree_finite_card_eq_finrank_cyclic
      F E g' hg'
  let :=
    CyclicCohomology.isCyclic_of_generator g hg
  let : CommGroup Q := IsCyclic.commGroup
  let :=
    CyclicCohomology.isCyclic_of_generator g' hg'
  let : CommGroup (Gal(E / F)) := IsCyclic.commGroup
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let U :=
    Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E)
  let eM : M ≅ Rep.res eQ.toMonoidHom U := by
    refine Rep.mkIso (Representation.Equiv.mk (rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal).toIntLinearEquiv ?_)
    intro q
    apply LinearMap.ext
    intro x
    exact
      rationalAbstractExtensionIdeleClassEquiv_action
        K L hLK hnormal q x
  let eTateH0 :=
    TateCohomology.isoFiniteCyclicZero M g hg ≪≫ ((normHomCompSubHomologyIsoOfRepIso eM g) ≪≫
      normHomCompSubHomologyResEquivIso eQ U g) ≪≫
      (TateCohomology.isoFiniteCyclicZero U g' hg').symm
  let eTateHm1 :=
    TateCohomology.isoFiniteCyclicNegOne M g hg ≪≫ ((subCompNormHomHomologyIsoOfRepIso eM g) ≪≫
      subCompNormHomHomologyResEquivIso eQ U g) ≪≫
      (TateCohomology.isoFiniteCyclicNegOne U g' hg').symm
  let := hIdeleClassTateCard.1
  let := hIdeleClassTateCard.2.1
  let :=
    Finite.of_equiv
      (tateCohomology U 0) eTateH0.symm.toLinearEquiv.toEquiv
  let : Finite (tateCohomology M (-1)) :=
    Finite.of_equiv
      (tateCohomology U (-1)) eTateHm1.symm.toLinearEquiv.toEquiv
  refine
    { finiteTateHZero := by
        change Finite (tateCohomology M 0)
        infer_instance
      finiteTateHMinusOne := by
        change Finite (tateCohomology M (-1))
        infer_instance
      tateHZero_card := ?_
      tateHMinusOne_card := ?_ }
  · calc
      _ =
          Nat.card (tateCohomology U 0) :=
        Nat.card_congr eTateH0.toLinearEquiv.toEquiv
      _ = Module.finrank F E := hIdeleClassTateCard.2.2.1
      _ =
          ((DegreeData.FiniteAbstractExtension.ofInclusion
            L K hLK).degree : ℕ) :=
        (finiteAbstractExtension_degree_eq_finrank
          ℚ (SeparableClosure ℚ) K L hLK hnormal
            hKfinite hfinite).symm
  · calc
      _ =
          Nat.card (tateCohomology U (-1)) :=
        Nat.card_congr eTateHm1.toLinearEquiv.toEquiv
      _ = 1 := hIdeleClassTateCard.2.2.2

end Reciprocity

end
end GlobalClassFieldTheory
