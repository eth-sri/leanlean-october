module

public import Mathlib.GroupTheory.Abelianization.Defs
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeWitnessComparison
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidue

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Ambient prime comparison

The local Artin map and the ambient embedded norm-residue construction
agree on norm classes and therefore agree pointwise.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel
open scoped IsMulCommutative

variable (K F E : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E] [FiniteDimensional K F]
    [Algebra.IsSeparable K F]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation F)]
    [FiniteDimensional F E] [IsAbelianGalois F E] (j : E →ₐ[K] SeparableClosure K)
    (e : ambientEmbeddedSeparableClosureEquiv K F E j)

/-- Every abelianized Galois element is simultaneously represented by the local
Artin map and by the ambient embedded norm-residue construction. -/
theorem
    exists_localArtin_ambientEmbedded_prime
    (z : Abelianization Gal(E / F)) :
    ∃ x : Fˣ,
      localArtinMonoidHom F E x = z ∧
        ambientEmbeddedNormResidueAbelianElement K F E j e x = z := ⟨ambientEmbeddedPrimeWitness K F E j e z,
      ambientEmbeddedPrimeWitness_local K F E j e z,
      ambientEmbeddedPrimeWitness_ambient K F E j e z⟩

/-- The ambient embedded norm-residue element depends only on the unit's norm
class modulo norms from `E`. -/
theorem
    ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq
    (a x : Fˣ)
    (h : normClass F E a = normClass F E x) :
    ambientEmbeddedNormResidueAbelianElement K F E j e a =
      ambientEmbeddedNormResidueAbelianElement K F E j e x := by
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let :=
    i.toRingHom.toAlgebra
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ⟨algebraMap F E z, rfl⟩
  let hTargetNormal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let hTargetFinite :=
    ambientEmbeddedExtensionQuotient_finite K F E j e
  let hHabsolute := ambientEmbeddedAbsoluteQuotientFinite K F i
  let F₀ :=
    abstractFixedField K (SeparableClosure K) H₀
  let phiF :=
    (i.equivFieldRange).trans
      (IntermediateField.equivOfEq (InfiniteGalois.fixedField_fixingSubgroup
        (AlgHom.fieldRange i)).symm)
  let E₀ :=
    abstractRelativeFixedField K (SeparableClosure K) hJH
  have hfixedE :=
    InfiniteGalois.fixedField_fixingSubgroup
      (AlgHom.fieldRange j)
  let phiE : E ≃+* E₀ := by
    change
      E ≃+*
        abstractFixedField K (SeparableClosure K) J₀
    exact
      ((j.equivFieldRange).trans
        (IntermediateField.equivOfEq hfixedE.symm)).toRingEquiv
  let q₀ :=
    abstractExtensionQuotientEquivGaloisGroup
      K (SeparableClosure K) H₀ J₀ hJH hTargetNormal
  let qE :=
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
      K F E j e
  let aF0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv a
  let xF0 : F₀ˣ :=
    Units.mapEquiv phiF.toMulEquiv x
  have hnormClass0 :
      normClass F₀ E₀ aF0 =
        normClass F₀ E₀ xF0 := by
    exact
      normClass_mapEquiv F E F₀ E₀
        phiF.toRingEquiv phiE
        (by
          apply RingHom.ext
          intro y
          rfl)
        a x h
  let abstractFixedFieldNormResidueSymbol₀ := abstractFixedFieldNormResidueSymbol K (SeparableClosure K) (localResidueDatum K) (localHenselianValuation K) (separableClosureUnits_isClassFormation K) H₀ J₀ hJH
  have hambientSame :
      abstractFixedFieldNormResidueSymbol₀ (Additive.ofMul aF0) =
        abstractFixedFieldNormResidueSymbol₀ (Additive.ofMul xF0) :=
    abstractFixedFieldNormResidueSymbol_eq_of_normClass_eq
      K (SeparableClosure K)
      (localResidueDatum K)
      (localHenselianValuation K)
      (separableClosureUnits_isClassFormation K)
      H₀ J₀ hJH aF0 xF0 hnormClass0
  change
    qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol₀ (Additive.ofMul aF0)))) =
      qE.abelianizationCongr
        (q₀.abelianizationCongr.symm
          (Additive.toMul
            (abstractFixedFieldNormResidueSymbol₀ (Additive.ofMul xF0))))
  rw [hambientSame]

/-- For an embedded finite abelian local extension, the abelian local Artin
map agrees pointwise with the ambient norm-residue element transported through
a separable-closure equivalence. -/
theorem
    abelianLocalArtin_eq_ambientEmbeddedNormResidueSymbol_of_equiv
    (a : Fˣ) :
    abelianLocalArtinMonoidHom F E a =
      ambientEmbeddedNormResidueElement K F E j e a := by
  obtain ⟨x, hxLocal, hxAmbient⟩ :=
    exists_localArtin_ambientEmbedded_prime K F E j e
      (localArtinMonoidHom F E a)
  let :=
    (j.comp (IsScalarTower.toAlgHom K F E)).toRingHom.toAlgebra
  let jI :=
    e.symm.toAlgHom.comp ({ j with commutes' := fun y => rfl})
  have hnormClass :
      normClass F E a = normClass F E x := by
    apply
      (concreteReciprocityEquivOfEmbedding
        F E jI
        (localResidueDatum F)
        (localHenselianValuation F)
        (separableClosureUnits_isClassFormation F)).symm.injective
    change
      concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) a =
        concreteNormResidueSymbolOfEmbedding
          F E jI
          (localResidueDatum F)
          (localHenselianValuation F)
          (separableClosureUnits_isClassFormation F) x
    rw [← (DFunLike.congr_fun
      (localArtinMonoidHom_eq_of_embedding F E jI) a), ← (DFunLike.congr_fun
      (localArtinMonoidHom_eq_of_embedding F E jI) x)]
    exact hxLocal.symm
  change
    (Abelianization.equivOfComm).symm
        (localArtinMonoidHom F E a) =
      (Abelianization.equivOfComm).symm
        (ambientEmbeddedNormResidueAbelianElement K F E j e a)
  apply congrArg (Abelianization.equivOfComm).symm
  calc
    _ =
        ambientEmbeddedNormResidueAbelianElement K F E j e x :=
      hxAmbient.symm
    _ = ambientEmbeddedNormResidueAbelianElement K F E j e a :=
      (ambientEmbeddedNormResidueAbelianElement_eq_of_normClass_eq
        K F E j e a x hnormClass).symm

end LocalClassFieldTheory

end
