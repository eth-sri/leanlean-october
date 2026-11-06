module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormProof

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Naturality of finite-Galois global reciprocity in abelianizations

For a finite tower `K ⊆ M ⊆ N` with `N / K` Galois, this file proves
that ordinary idèle-class norm from `M` to `K` corresponds to restriction
from `Gal(N / M)` to `Gal(N / K)`, after passing both Galois groups to their
abelianizations.  The intermediate extension `M / K` is not assumed Galois.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open LocalClassFieldTheory
open KummerTheory
open CyclicCohomology

 theorem abelianizationNaturalityIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] abelianizationNaturalityIdeleClassIsMulCommutative

/-- Transport by an equality-induced field equivalence leaves the underlying
rational direct-limit idèle class unchanged. -/
private theorem rationalIdeleClassEquivFixed_congr_apply_val
    {A B : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (h : A = B)
    (e : B ≃ₐ[ℚ] A)
    (he : e.trans (IntermediateField.equivOfEq h) =
      (AlgEquiv.refl : B ≃ₐ[ℚ] B))
    (c : Additive (IdeleClassGroup B)) :
    ((rationalIdeleClassEquivFixed A)
        (MulEquiv.toAdditive (ideleClassCongr e) c)).1 =
      ((rationalIdeleClassEquivFixed B) c).1 := by
  cases h
  have he' : e = AlgEquiv.refl := by
    apply AlgEquiv.ext
    intro x
    have hx := DFunLike.congr_fun he x
    change e x = x at hx
    exact hx
  rw [he']
  have hc :
      MulEquiv.toAdditive
          (ideleClassCongr (AlgEquiv.refl : A ≃ₐ[ℚ] A)) c = c := by
    cases c with
    | ofMul c =>
        exact congrArg Additive.ofMul (ideleClassCongr_refl c)
  rw [hc]



section CommonTop

variable
    (K M N : Type)
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra M N] [Algebra K N]
    [IsScalarTower K M N]











/-- The abelianized quotient of an explicitly embedded finite Galois tower
is the abelianization of its actual Galois group. -/
noncomputable def
    numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    Additive
        (Abelianization
          (numberFieldEmbeddedFiniteGaloisSubextension K N j).extensionQuotient) ≃+
      Additive (Abelianization Gal(N / K)) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldEmbeddedExtensionQuotientEquivGaloisGroup K N j))

/-- The abstract norm-residue symbol followed by the actual Galois
abelianization comparison, with the public finite norm quotient's additive
structure fixed at this boundary. -/
 noncomputable def
    numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    [hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j))] :
    FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j) ≃+
      Additive (Abelianization Gal(N / K)) := by
  let _ : Finite _ :=
    (numberFieldEmbeddedFiniteAbstractField K N j).finite
  let _ :
      (extensionSubgroup
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)).Normal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  letI : AddCommGroup
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    finiteNormQuotientAddCommGroup rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
  exact
    @AddEquiv.trans
      (FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j))
      (Additive
        (Abelianization
          (numberFieldEmbeddedFiniteGaloisSubextension K N j).extensionQuotient))
      (Additive (Abelianization Gal(N / K)))
      inferInstance inferInstance inferInstance
      (rationalCyclotomicDegreeData.normResidueSymbol
        rationalIdeleClassRepresentation
        rationalCyclotomicIdeleClassValuationData
        rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
        (numberFieldEmbeddedFiniteAbstractField K N j)
        (numberFieldEmbeddedFiniteGaloisSubextension K N j))
      (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
        K N j)

/-- Evaluation of the typed embedded norm-residue/Galois comparison. -/
private theorem
    numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv_apply
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    [hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j))]
    (x : FiniteNormQuotient rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :
    numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv K N j x =
      numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
        K N j
        (rationalCyclotomicDegreeData.normResidueSymbol
          rationalIdeleClassRepresentation
          rationalCyclotomicIdeleClassValuationData
          rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
          (numberFieldEmbeddedFiniteAbstractField K N j)
          (numberFieldEmbeddedFiniteGaloisSubextension K N j) x) := by
  let hBaseFinite :=
    (numberFieldEmbeddedFiniteAbstractField K N j).finite
  let hExtensionNormal :=
    numberFieldEmbeddedExtensionSubgroup_normal K N j
  rfl

/-- The finite-Galois norm-residue map built from an explicitly supplied
embedding of the top field, with target the actual Galois abelianization. -/
noncomputable def globalNormResidueAbelianizationMonoidHomOfEmbedding
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ) :
    IdeleClassGroup K →* Abelianization Gal(N / K) := by
  let hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  let e :
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K N).range) ≃*
        Abelianization Gal(N / K) :=
    AddEquiv.toMultiplicative
      ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm.trans
        (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
          K N j (hRelativeFinite := hRelativeFinite)))
  exact e.toMonoidHom.comp
    (QuotientGroup.mk' (_root_.ideleClassNorm K N).range)

/-- Evaluation of the explicitly embedded abelianized norm-residue map on
an ordinary idèle class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHomOfEmbedding_apply
    [FiniteDimensional K N] [IsGalois K N]
    (j : N →ₐ[ℚ] SeparableClosure ℚ)
    (c : IdeleClassGroup K) :
    letI _ : Finite
        ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
          extensionSubgroup
            (numberFieldEmbeddedBaseSubgroup K N j)
            (numberFieldEmbeddedTopSubgroup K N j)
            (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
      numberFieldEmbeddedExtensionQuotient_finite K N j
    globalNormResidueAbelianizationMonoidHomOfEmbedding K N j c =
      Additive.toMul
        (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
          K N j
          (rationalCyclotomicDegreeData.normResidueSymbol
            rationalIdeleClassRepresentation
            rationalCyclotomicIdeleClassValuationData
            rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
            (numberFieldEmbeddedFiniteAbstractField K N j)
            (numberFieldEmbeddedFiniteGaloisSubextension K N j)
            (finiteNormClass rationalIdeleClassRepresentation
              (numberFieldEmbeddedBaseSubgroup K N j)
              (numberFieldEmbeddedTopSubgroup K N j)
              (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
              (numberFieldEmbeddedIdeleClassEquivAmbientFixed
                K N j (Additive.ofMul c))))) := by
  dsimp only
  let hRelativeFinite : Finite
      ((numberFieldEmbeddedBaseSubgroup K N j).toSubgroup ⧸
        extensionSubgroup
          (numberFieldEmbeddedBaseSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup K N j)
          (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)) :=
    numberFieldEmbeddedExtensionQuotient_finite K N j
  have hclass :=
    numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K N j c
  let x :
      FiniteNormQuotient rationalIdeleClassRepresentation
        (numberFieldEmbeddedBaseSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup K N j)
        (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j) :=
    finiteNormClass rationalIdeleClassRepresentation
      (numberFieldEmbeddedBaseSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup K N j)
      (numberFieldEmbeddedTopSubgroup_le_baseSubgroup K N j)
      (numberFieldEmbeddedIdeleClassEquivAmbientFixed
        K N j (Additive.ofMul c))
  let q : Additive
      (IdeleClassGroup K ⧸ (_root_.ideleClassNorm K N).range) :=
    Additive.ofMul
      (QuotientGroup.mk' (_root_.ideleClassNorm K N).range c)
  have hclass' :
      numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j x = q :=
    hclass
  have htransport :
      (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm q = x := by
    exact
      (congrArg
        (numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm hclass'.symm).trans
        ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
          K N j).symm_apply_apply x)
  calc
    globalNormResidueAbelianizationMonoidHomOfEmbedding K N j c =
        Additive.toMul
          (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
            K N j (hRelativeFinite := hRelativeFinite)
            ((numberFieldEmbeddedFiniteNormQuotientEquivIdeleClassNormQuotient
              K N j).symm q)) := by
      rfl
    _ =
        Additive.toMul
          (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
            K N j (hRelativeFinite := hRelativeFinite) x) :=
      congrArg
        (fun y =>
          Additive.toMul
            (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv
              K N j (hRelativeFinite := hRelativeFinite) y))
        htransport
    _ =
        Additive.toMul
          (numberFieldEmbeddedAbelianizedExtensionQuotientEquivGaloisAbelianization
            K N j
            (rationalCyclotomicDegreeData.normResidueSymbol
              rationalIdeleClassRepresentation
              rationalCyclotomicIdeleClassValuationData
              rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
              (numberFieldEmbeddedFiniteAbstractField K N j)
              (numberFieldEmbeddedFiniteGaloisSubextension K N j) x)) := by
      exact congrArg Additive.toMul
        (numberFieldEmbeddedAbstractNormResidueGaloisAbelianizationEquiv_apply
          K N j (hRelativeFinite := hRelativeFinite) x)











end CommonTop

end Reciprocity
end GlobalClassFieldTheory

end
