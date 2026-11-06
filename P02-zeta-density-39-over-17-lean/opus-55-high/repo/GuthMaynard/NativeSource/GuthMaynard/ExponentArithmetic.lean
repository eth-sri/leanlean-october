module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import GuthMaynard.NativeSource.GuthMaynard.ZeroDetector

@[expose] public section

open Filter Asymptotics

namespace GuthMaynard.NativeMoment

/-- The `alpha` definition used by the source-facing construction in `ExponentArithmetic`. -/
noncomputable def alpha (σ : ℝ) : ℝ := 15 * (1 - σ) / ((3 + 5 * σ) * (18/5 - 4 * σ))
