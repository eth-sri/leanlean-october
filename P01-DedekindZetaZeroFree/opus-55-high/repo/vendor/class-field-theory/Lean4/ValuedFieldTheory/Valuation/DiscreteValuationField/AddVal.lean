module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Normalized additive valuations on discrete valuation rings

This file supplies general-purpose facts about Mathlib's normalized additive
valuation on a discrete valuation ring which are independent of any chosen
valued-field presentation.
-/


universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Membership in a power of the maximal ideal is detected by the normalized
additive valuation. -/
theorem mem_maximalIdeal_pow_iff_addVal_ge (a : R) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow]
