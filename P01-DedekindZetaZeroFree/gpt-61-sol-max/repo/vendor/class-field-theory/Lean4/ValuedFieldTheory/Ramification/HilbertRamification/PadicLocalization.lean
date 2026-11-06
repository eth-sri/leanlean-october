module

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core
public import ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
public import ValuedFieldTheory.Valuation.Completion.Padic
public import ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionFieldLocalization
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/









set_option autoImplicit false

/-!
# Localizations at rational p-adic absolute values

This file collects the reusable algebra, finiteness, Galois, and
nonarchimedean facts needed to compare a global algebraic localization with
an extension of `ℚ_[p]`.
-/

noncomputable section

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

















variable (p : ℕ) [Fact p.Prime]
variable (L : Type) [Field L] [Algebra ℚ L]
  [FiniteDimensional ℚ L] [IsAbelianGalois ℚ L]



















































/-- The rational `p`-adic absolute value is nonarchimedean in the bounded
natural-number sense used by the ramification API. -/
theorem rationalPadicAbsoluteValue_nonarchimedean :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue
      (Rat.AbsoluteValue.padic p) := by
  apply LubinTate.Valuations.nonarchimedean_of_strong_triangle
  intro x y
  change
    ((padicNorm p (x + y) : ℚ) : ℝ) ≤
      max ((padicNorm p x : ℚ) : ℝ) ((padicNorm p y : ℚ) : ℝ)
  exact_mod_cast padicNorm.nonarchimedean

end HilbertRamification

end
