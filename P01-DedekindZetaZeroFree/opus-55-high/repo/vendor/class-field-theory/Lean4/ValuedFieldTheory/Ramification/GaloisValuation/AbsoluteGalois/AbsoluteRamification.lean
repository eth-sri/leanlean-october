module

public import ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


namespace RamificationTheory

open ValuationTheory

/-!
# Absolute Galois ramification

This file develops the decomposition and inertia subgroups of an absolute
Galois group after the finite-level valuation-restriction layer.
-/

noncomputable section

universe u v w z

namespace Field
namespace absoluteGaloisGroup

open scoped Topology Pointwise
open CategoryTheory

section AbsoluteRamification

variable (K : Type u) [Field K]

/-- Provides the instance `absoluteGaloisGroupMulSemiringActionAlgebraicClosure`. -/
instance absoluteGaloisGroupMulSemiringActionAlgebraicClosure :
    MulSemiringAction
      (Field.absoluteGaloisGroup K) (AlgebraicClosure K) := by
  change MulSemiringAction
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (AlgebraicClosure K)
  infer_instance
