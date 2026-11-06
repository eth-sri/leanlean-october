module

public import Mathlib

@[expose] public section

/-! Exact algebra of the rate parameters in Section 2. These theorems do not
assume or assert that the defined rate is the minimax risk. -/

noncomputable section

namespace RoughRegime.Rates

def rho (lo hi : ℝ) : ℝ :=
  (Real.sqrt hi - Real.sqrt lo) / (Real.sqrt hi + Real.sqrt lo)

def tau (lo hi : ℝ) : ℝ := -Real.log (rho lo hi)

end RoughRegime.Rates
