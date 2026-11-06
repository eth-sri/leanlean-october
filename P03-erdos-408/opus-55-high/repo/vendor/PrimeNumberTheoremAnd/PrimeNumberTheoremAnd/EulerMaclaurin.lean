module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.NumberTheory.AbelSummation

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

@[expose] public section


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


