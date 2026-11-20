module

public import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Low-degree Herbrand equivalences for a localized completion
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

variable (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial) (w : AbsoluteValueExtension vK ell)

/-- Degree-zero multiplicative Herbrand cohomology for a decomposition group
identified with degree-zero Tate cohomology of the localized field units. -/
noncomputable def localHerbrandH0EquivUnitsTateH0 :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      Multiplicative
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  letI :
      MulDistribMulAction
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w)
        (LocalizedCompletion vK w)ˣ :=
    galoisGroupFieldUnitsMulDistribMulAction
      vK.Completion (LocalizedCompletion vK w)
  exact
    (herbrandH0CompMulEquiv
       (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w)).trans
      ((herbrandH0MulEquivInvariantsNormQuotient
        vK.Completion (LocalizedCompletion vK w)).trans
          ((tateUnitsH0IsoInvariantsQuotient
            vK.Completion
            (LocalizedCompletion vK w)).symm.toLinearEquiv.toAddEquiv).toMultiplicative)

/-- Degree-minus-one multiplicative Herbrand cohomology for a decomposition
group identified with degree-minus-one Tate cohomology of localized units. -/
noncomputable def localHerbrandHMinusOneEquivUnitsTateHminusOne
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ) :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1) σ hgen) ≃
      tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) (-1) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  letI :
      MulDistribMulAction
        (LocalizedCompletion vK w ≃ₐ[vK.Completion]
          LocalizedCompletion vK w)
        (LocalizedCompletion vK w)ˣ :=
    galoisGroupFieldUnitsMulDistribMulAction
      vK.Completion (LocalizedCompletion vK w)
  exact
    (herbrandHMinusOneCompMulEquiv

      (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w) (subgroupGeneratorOfGenerator
        (absoluteValueDecompositionGroup k w.1) σ hgen)).toEquiv.trans
      (herbrandHminusOneEquivUnitsTateHminusOne
        vK.Completion (LocalizedCompletion vK w)
        (localizedCompletionGaloisGenerator
          vK hvK w σ hgen) (localizedCompletionGaloisGenerator_generates
          vK hvK w σ hgen))

/-- Degree-zero Herbrand cohomology for a decomposition group identified with
the norm quotient of the localized field extension. -/
noncomputable def localHerbrandH0EquivNormQuotient :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      NormQuotient vK.Completion
        (LocalizedCompletion vK w) := by
  letI := localizedCompletionBaseAlgebra vK w
  letI := localizedCompletionGlobalAlgebra vK w
  letI := localizedCompletionIsScalarTower vK w
  letI : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  letI : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  letI := localizedCompletionDecompositionGroupFintype vK w
  exact (localHerbrandH0EquivUnitsTateH0 vK hvK w).trans <|
    ((H0TateUnitsIsoNormQuotient
      vK.Completion
      (LocalizedCompletion vK w)).toLinearEquiv.toAddEquiv).toMultiplicative.trans <|
      MulEquiv.multiplicativeAdditive
        (NormQuotient vK.Completion
          (LocalizedCompletion vK w))

end LocalTateComparison

end LocalClassFieldTheory

end
