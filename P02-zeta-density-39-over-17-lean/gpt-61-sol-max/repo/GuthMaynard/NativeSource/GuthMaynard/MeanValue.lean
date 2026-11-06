module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import GuthMaynard.NativeSource.GuthMaynard.Separated

@[expose] public section

open Complex Finset
open scoped BigOperators

namespace GuthMaynard.NativeMoment

/--
The discrete Dirichlet-polynomial mean-value input used in Section 13.1.

The existentially quantified `C` is an absolute constant: it is chosen before
the polynomial length, height, separated set, and coefficients. This represents
the implied constant in the paper's `≲` notation rather than incorrectly fixing
that constant to one.
-/
def MontgomeryMeanValue : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
      0 < N → 1 ≤ T →
      IsSeparated 1 W →
      InBaseInterval T W →
      ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 ≤
        C * (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2


