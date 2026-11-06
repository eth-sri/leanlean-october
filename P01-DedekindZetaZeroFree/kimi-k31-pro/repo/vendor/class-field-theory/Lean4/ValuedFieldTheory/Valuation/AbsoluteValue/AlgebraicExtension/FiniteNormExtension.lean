module

public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/








set_option autoImplicit false

/-!
# Finite-extension norm formula for complete valuations

The nonarchimedean branch uses mathlib's spectral norm.  The archimedean branch
uses the completed Ostrowski theorem, reducing the statement to the
standard `ℝ` and `ℂ` absolute values.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations















































/-- The nontrivial-valuation convention excludes the trivial valuation in the nontrivial-valuation convention; for the
nonarchimedean spectral branch this supplies the corresponding mathlib
`NontriviallyNormedField` instance on `WithAbs v`. -/
@[reducible]  def finiteWithAbsNontriviallyNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    NontriviallyNormedField (WithAbs v) :=
  NontriviallyNormedField.ofNormNeOne
    (by
      rcases hv with ⟨x, hx0, hx1⟩
      refine ⟨WithAbs.toAbs v x, ?_, ?_⟩
      · intro hx
        apply hx0
        simpa using congrArg (WithAbs.equiv v) hx
      · simpa [WithAbs.norm_eq_apply_ofAbs] using hx1)

/-- `WithAbs` is only a type synonym, so algebraicity is transported from the
original base field without adding data. -/
 instance finiteWithAbsAlgebraIsAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    Algebra.IsAlgebraic (WithAbs v) L := by
  exact Algebra.IsAlgebraic.tower_top
    (K := K) (L := WithAbs v) (A := L)











 

 


































/-- Explicit result package for the finite-degree norm construction, finite nonarchimedean case:
the unique extension is the norm formula and the finite extension is complete. -/
structure FiniteNormExtensionFiniteExtensionResult
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) where
  /-- The distinguished absolute value on the finite extension. -/
  extension : AbsoluteValue L ℝ
  /-- The distinguished absolute value restricts to the given base absolute value. -/
  extends_base : ∀ x : K, extension (algebraMap K L x) = v x
  /-- Every extension of the base absolute value equals the distinguished extension. -/
  unique :
    ∀ w : AbsoluteValue L ℝ,
      (∀ x : K, w (algebraMap K L x) = v x) → w = extension
  /-- The distinguished extension is given by the finite-extension norm formula. -/
  norm_formula : ∀ x : L, extension x = finiteExtensionNormFormulaValue v x
  /-- The distinguished extension is complete. -/
  complete_extension : IsCompleteForAbsoluteValue extension























end Valuations
end AlgebraicNumberTheory

end
