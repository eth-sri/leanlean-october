module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Separable closures over the small local-field representative

The existing separable closure of `K` is also a separable closure of
`Shrink.{0} K` after transporting the base-field embedding.  This gives a
compatible equivalence with Mathlib's chosen separable closure of `Shrink K`.
-/

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The original separable closure, regarded as an extension of the small
representative of its base field. -/
@[reducible]
noncomputable def shrinkSeparableClosureAlgebra :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    Algebra (Shrink.{0} K) (SeparableClosure K) := by
  letI : Small.{0} K := nonarchimedeanLocalField_small K
  exact ((algebraMap K (SeparableClosure K)).comp
    (Shrink.ringEquiv K).toRingHom).toAlgebra





end LocalFieldTheory

end
