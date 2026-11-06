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


/-!
# Finite-extension norm formula for complete valuations

The nonarchimedean branch uses mathlib's spectral norm.  The archimedean branch
uses the completed Ostrowski theorem, reducing the statement to the
standard `ℝ` and `ℂ` absolute values.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- `WithAbs` is only a type synonym, so algebraicity is transported from the
original base field without adding data. -/
 instance finiteWithAbsAlgebraIsAlgebraic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (v : AbsoluteValue K ℝ) :
    Algebra.IsAlgebraic (WithAbs v) L := 
  Algebra.IsAlgebraic.tower_top
    (K := K) (L := WithAbs v) (A := L)
