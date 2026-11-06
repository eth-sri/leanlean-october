module
import Mathlib
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







/- Actual truncated Möbius divisor sum
   `∑_{d ∣ n, d ≤ 2 T^(1/100)} μ(d)`. -/




/- The classical epsilon-power bound for the number of positive divisors.
    The constant may depend on `ε` but is uniform in positive `n`. -/
def DivisorCountBoundProp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε




