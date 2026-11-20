module
public import GuthMaynard.NativeSource.GuthMaynard.ZeroCount
public import GuthMaynard.NativeSource.GuthMaynard.Asymptotics
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.Divisors

@[expose] public section

open Complex
open scoped BigOperators
open Classical

namespace GuthMaynard.NativeMoment

/-- One past the natural-number floor of the detector's divisor cutoff. -/
noncomputable def detectorCutoff (T : ℝ) : ℕ :=
  ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ + 1

/-- The exact finite support of the truncated Möbius sum in the divisor variable. -/
noncomputable def detectorDivisors (n : ℕ) (T : ℝ) : Finset ℕ :=
  n.divisors.filter (fun d => (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ))

@[simp]
lemma mem_detectorDivisors {d n : ℕ} {T : ℝ} :
    d ∈ detectorDivisors n T ↔
      (d ∣ n ∧ n ≠ 0) ∧ (d : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
  simp [detectorDivisors, Nat.mem_divisors]

/- Actual truncated Möbius divisor sum
   `∑_{d ∣ n, d ≤ 2 T^(1/100)} μ(d)`. -/
/-- The `mobius_sum` definition used by the source-facing construction in `ZeroDetector`. -/
-- Source-equation compatibility keeps this established public name.
@[nolint defsWithUnderscore]
noncomputable def mobius_sum (n : ℕ) (T : ℝ) : ℂ :=
  ∑ d ∈ detectorDivisors n T, (ArithmeticFunction.moebius d : ℂ)

/-- The `detectorCoeff` definition used by the source-facing construction in `ZeroDetector`. -/
noncomputable def detectorCoeff (n : ℕ) (T : ℝ) : ℂ :=
  (mobius_sum n T) * Real.exp (-(n : ℝ) / (T ^ (1/2 : ℝ)))

/-- The classical epsilon-power bound for the number of positive divisors.
    The constant may depend on `ε` but is uniform in positive `n`. -/
def DivisorCountBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε

@[simp]
lemma detectorCoeff_eq_zero_iff (n : ℕ) (T : ℝ) :
    detectorCoeff n T = 0 ↔ mobius_sum n T = 0 := by
  rw [detectorCoeff, mul_eq_zero]
  simp

end GuthMaynard.NativeMoment
