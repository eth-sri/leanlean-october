module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.SeparableClosure
public import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

/-!
# Finite local reciprocity: realizing finite Galois extensions in a separable closure

Every finite Galois extension `L/K` is embedded into the chosen separable
closure of `K`.  Its image supplies the concrete closed subgroup used by the
abstract class-field theory.  The resulting abstract fixed coefficient group
is `Lˣ`, and the resulting abstract extension quotient is the actual
`Gal(L/K)`.

No perfectness hypothesis is imposed; this includes equal-characteristic
local fields such as finite extensions of `𝔽_q((t))`.
-/

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Realization relative to an explicit embedding -/

/-- The embedded copy of `L` determined by an explicit embedding into the
fixed separable closure.  Keeping the embedding visible is what makes the
canonicity argument in the finite local reciprocity theorem meaningful. -/
def finiteGaloisFieldRangeOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange i

/-- An explicit embedding identifies `L` with its field range. -/
def finiteGaloisFieldRangeEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] finiteGaloisFieldRangeOfEmbedding K L i :=
  AlgEquiv.ofInjectiveField i

/-- The image of an embedded finite Galois extension is again Galois over the base field. -/
instance finiteGaloisFieldRangeOfEmbedding_isGalois
    (i : L →ₐ[K] SeparableClosure K) :
    IsGalois K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquivOfEmbedding K L i)

/-- The image of an embedded finite extension is finite-dimensional over the base field. -/
instance finiteGaloisFieldRangeOfEmbedding_finiteDimensional
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).toLinearEquiv.finiteDimensional

/-- The closed fixing subgroup attached to an explicit realization of
`L/K` in the separable closure. -/
def finiteGaloisClosedFixingSubgroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ClosedSubgroup (Gal(SeparableClosure K / K)) :=
  closedFixingSubgroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The fixing subgroup of an embedded finite Galois extension is normal in the absolute subgroup. -/
instance finiteGaloisExtensionSubgroupOfEmbedding_normal
    (i : L →ₐ[K] SeparableClosure K) :
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal := by
  change
    (extensionSubgroup
      (closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K)))
      (closedFixingSubgroup K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))
      (fixingSubgroupLeBase K (SeparableClosure K)
        (finiteGaloisFieldRangeOfEmbedding K L i))).Normal
  infer_instance

/-- The abstract class-formation extension quotient attached to an explicit realization
of `L/K` is the actual relative Galois group. -/
def finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ((closedFixingSubgroup K (SeparableClosure K)
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      extensionSubgroup
        (closedFixingSubgroup K (SeparableClosure K)
          (⊥ : IntermediateField K (SeparableClosure K)))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i)
        (fixingSubgroupLeBase K (SeparableClosure K)
          (finiteGaloisFieldRangeOfEmbedding K L i))) ≃*
      Gal(L / K) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)).trans
      (AlgEquiv.autCongr
        (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm
