module

public import Mathlib.FieldTheory.Galois.Basic
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.FixedFieldNormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Intrinsic fixed-field specialization

This module specializes the embedded subgroup and inertia comparisons to actual finite fixed fields and packages the intrinsic Frobenius quotient.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- The type of algebra equivalences from the intrinsic separable closure of a
finite fixed field to the ambient separable closure. -/
abbrev intrinsicFixedFieldSeparableClosureEquiv
    (K : Type) [Field K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K)) :=
  let F := abstractFixedField K (SeparableClosure K) H.field
  @AlgEquiv F (SeparableClosure F) (SeparableClosure K)
    _ _ _
    (separableClosure F (AlgebraicClosure F)).algebra
    F.val.toRingHom.toAlgebra
