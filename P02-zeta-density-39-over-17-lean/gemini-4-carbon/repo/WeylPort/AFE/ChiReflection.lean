module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.Objects
public import WeylPort.Reflection
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Functional equation and conjugation for the actual AFE remainder

The zeta conjugation theorem is reused directly from the existing node-71 foundation.
The chi convention is the literal product in the paper, with principal complex powers.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped BigOperators ComplexConjugate

/-- Combining the two positive real bases preserves the paper's chi convention. -/
theorem chi_eq_two_mul (s : ℂ) :
    chi s = 2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Gamma (1 - s) *
      sin ((Real.pi : ℂ) * s / 2) := by
  have hpow := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    Real.pi_pos.le (s - 1)
  norm_num only [ofReal_ofNat] at hpow
  rw [hpow]
  have htwo : (2 : ℂ) ^ s = 2 * (2 : ℂ) ^ (s - 1) := by
    conv_lhs => rw [show s = s - 1 + 1 by ring]
    rw [cpow_add _ _ (by norm_num), cpow_one]
    ring
  simp only [chi, htwo]
  ring

end DhimanKadiriQuesadaHerrera2026
