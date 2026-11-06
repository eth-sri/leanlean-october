module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# The global norm-residue symbol for finite Galois extensions

For an arbitrary finite Galois extension of number fields, the global
norm-residue quotient is the abelianization of the genuine Galois group:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`.

The abelian specialization in `GlobalNormResidue` identifies this target
further with `Gal(L / K)`.  This file retains the abelianization and therefore
states global reciprocity at its full finite-Galois generality.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Idèle classes are commutative.  Keeping the mixin as a named local
instance lets norm-range quotient types elaborate before entering a
declaration body. -/
local instance
    globalNormResidueAbelianization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The abelianization of the compatible abstract extension quotient is the
abelianization of the actual Galois group. -/
noncomputable def
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization :
    Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))) ≃+
      Additive (Abelianization (Gal(L / K))) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L))






























/-- The abstract norm-residue symbol followed by the concrete Galois
comparison.  This declaration boundary keeps the dependent quotient indices
and their instance packages from being reconstructed at each evaluation. -/
 noncomputable def
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv :
    FiniteNormQuotient rationalIdeleClassRepresentation
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      Additive (Abelianization (Gal(L / K))) := by
  let _ : Finite _ :=
    (numberFieldTowerReciprocityFiniteAbstractField K L).finite
  let _ :
      (CyclicCohomology.extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
    numberFieldTowerExtensionSubgroup_normal K L
  let _ : Finite _ :=
    (numberFieldTowerFiniteGaloisSubextension K L).finite
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
      (Additive
        (Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))))
      (Additive (Abelianization (Gal(L / K))))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (numberFieldTowerReciprocityFiniteAbstractField K L)
        (numberFieldTowerFiniteGaloisSubextension K L))
      (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L)

/-- The actual global norm-residue equivalence for a finite Galois
number-field extension:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`. -/
noncomputable def globalNormResidueAbelianizationEquiv :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive (Abelianization (Gal(L / K))) := by
  exact
    (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
        K L).symm.trans
      (numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L)


























































































































































/-- The genuine global norm-residue homomorphism with target the
abelianization of the actual Galois group. -/
noncomputable def globalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →*
      Abelianization (Gal(L / K)) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Abelianization (Gal(L / K)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  exact
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range)

/-- Evaluation of the finite-Galois global norm-residue homomorphism is the
global equivalence applied to the genuine norm quotient class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c =
      Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K L).range c))) :=
  rfl

















































































































/-- The finite-Galois global norm-residue symbol viewed on the idele group.

This is the genuine idele-class symbol pulled back along
`I_K → C_K`; in particular it is not a separately chosen map. -/
noncomputable def globalNormResidueAbelianizationIdeleMonoidHom :
    IdeleGroup K →*
      Abelianization (Gal(L / K)) :=
  (globalNormResidueAbelianizationMonoidHom K L).comp
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))

/-- Evaluation of the finite-Galois norm-residue symbol on an idele is
evaluation of the class symbol on its genuine idele class. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_apply
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a =
      globalNormResidueAbelianizationMonoidHom K L
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K) a) :=
  rfl




















































































































section AbelianSpecialization

variable
    (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]







































































































































































end AbelianSpecialization

end Reciprocity
end GlobalClassFieldTheory

end
