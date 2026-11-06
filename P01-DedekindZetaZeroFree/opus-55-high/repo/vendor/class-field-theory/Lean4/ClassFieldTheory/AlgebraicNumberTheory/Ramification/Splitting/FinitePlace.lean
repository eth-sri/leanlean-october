module

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import GaloisCohomology.GroupTheory.Finite

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Decomposition groups and complete splitting at finite places

For a finite Galois extension of number fields `L / K`, this file
attaches an actual decomposition subgroup to every finite place of
`K`.  The extension of the adic absolute value is the one constructed
in `LocalNormApproximation`; no place above `v` is supplied as an
additional hypothesis.

The stabilizer is identified with the automorphism group of the algebraic
localization. The finite-localization theorem supplies finite dimensionality,
so the order of
the decomposition group is exactly the local degree.  Consequently
complete splitting is equivalent both to cardinality one and to local
degree one.
-/

open scoped NumberField Classical
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable {K L : Type}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- The actual decomposition subgroup at the chosen extension of the
finite place `v`. -/
def finitePlaceDecompositionGroup
    (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (L ≃ₐ[K] L) :=
  absoluteValueDecompositionGroup K
    (chosenFinitePlaceExtension (L := L) v).1

/-- A finite place splits completely when its chosen decomposition
subgroup is trivial.  Conjugacy of extensions makes this independent
of the chosen extension, but the chosen representative gives a
concrete subgroup for subsequent constructions. -/
def FinitePlaceSplitsCompletely
    (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  finitePlaceDecompositionGroup
    (K := K) (L := L) v = ⊥

/-- The local degree at `v`, defined using the actual algebraic
localization selected above. -/
def finitePlaceLocalDegree
    (v : HeightOneSpectrum (𝓞 K)) : ℕ := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  letI hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  exact
    Module.finrank vK.Completion
      (LocalizedCompletion vK w)

/-- The decomposition-group localization equivalence together with the finite-localization theorem
the finite-localization theorem: the order of the decomposition group equals the local
degree. -/
theorem finitePlaceDecompositionGroup_card_eq_localDegree
    (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card
        (finitePlaceDecompositionGroup
          (K := K) (L := L) v) =
      finitePlaceLocalDegree
        (K := K) (L := L) v := by
  let vK :=
    NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let w :=
    chosenFinitePlaceExtension (L := L) v
  let hK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) w.1
  let : SMul K w.1.Completion := hK.toSMul
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let :=
    localizedCompletionGlobalAlgebra vK w
  let :=
    localizedCompletionIsScalarTower vK w
  let E :=
    LocalizedCompletion vK w
  let : FiniteDimensional vK.Completion E :=
    localizedCompletionModuleFinite vK hvK w
  let : IsGalois vK.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vK w
  calc
    Nat.card
        (finitePlaceDecompositionGroup
          (K := K) (L := L) v) =
        Nat.card
          (E ≃ₐ[vK.Completion] E) :=
      Nat.card_congr
        (decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK w).toEquiv
    _ = Module.finrank vK.Completion E :=
      IsGalois.card_aut_eq_finrank
        vK.Completion E
    _ = finitePlaceLocalDegree
        (K := K) (L := L) v := rfl

omit [FiniteDimensional K L] in
/-- A finite place splits completely exactly when its decomposition
group has one element. -/
theorem finitePlaceSplitsCompletely_iff_card_eq_one
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      Nat.card
          (finitePlaceDecompositionGroup
            (K := K) (L := L) v) = 1 := by
  unfold FinitePlaceSplitsCompletely
  simp

/-- Complete splitting is equivalent to local degree one. -/
theorem finitePlaceSplitsCompletely_iff_localDegree_eq_one
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePlaceSplitsCompletely
        (K := K) (L := L) v ↔
      finitePlaceLocalDegree
          (K := K) (L := L) v = 1 := by
  rw [finitePlaceSplitsCompletely_iff_card_eq_one,
    finitePlaceDecompositionGroup_card_eq_localDegree]

/-- In a nontrivial finite Galois extension, a place whose
decomposition group is the whole Galois group cannot split
completely. This bridges the cyclic prime-power criterion, where
"nonsplit" means full decomposition group, and the normal-closure criterion. -/
theorem finitePlace_not_splitsCompletely_of_decompositionGroup_eq_top
    (hdegree : 1 < Module.finrank K L)
    (v : HeightOneSpectrum (𝓞 K))
    (hfull :
      finitePlaceDecompositionGroup
          (K := K) (L := L) v = ⊤) :
    ¬ FinitePlaceSplitsCompletely
        (K := K) (L := L) v := by
  intro hsplit
  have htopbot :
      (⊤ : Subgroup (L ≃ₐ[K] L)) = ⊥ := by
    rw [← hfull]
    exact hsplit
  have hcard : Nat.card (L ≃ₐ[K] L) = 1 := by
    have h :=
      congrArg
        (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card H)
        htopbot
    simpa using h
  rw [IsGalois.card_aut_eq_finrank] at hcard
  omega


section Quotient

/-- The image of the finite-place decomposition subgroup in a group
quotient.  In the Galois correspondence this is the decomposition
group in the corresponding intermediate extension. -/
def finitePlaceDecompositionGroupInQuotient
    (v : HeightOneSpectrum (𝓞 K))
    (P : Subgroup (L ≃ₐ[K] L))
    [P.Normal] :
    Subgroup ((L ≃ₐ[K] L) ⧸ P) :=
  (finitePlaceDecompositionGroup
    (K := K) (L := L) v).map
      (QuotientGroup.mk' P)

omit [FiniteDimensional K L] in
/-- The quotient decomposition group is trivial exactly when the
original decomposition group is contained in the quotient kernel. -/
theorem finitePlaceDecompositionGroupInQuotient_eq_bot_iff
    (v : HeightOneSpectrum (𝓞 K))
    (P : Subgroup (L ≃ₐ[K] L))
    [P.Normal] :
    finitePlaceDecompositionGroupInQuotient
        (K := K) (L := L) v P = ⊥ ↔
      finitePlaceDecompositionGroup
          (K := K) (L := L) v ≤ P := by
  rw [finitePlaceDecompositionGroupInQuotient,
    Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
