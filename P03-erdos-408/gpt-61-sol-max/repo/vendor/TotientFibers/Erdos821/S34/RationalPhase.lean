module
import Batteries.Tactic.Alias
import Erdos821.P4Rat.RationalFourier

public import Erdos821.S34.LogMultiplier
public import Erdos821.P5.Basic

@[expose] public section

set_option autoImplicit false

namespace Erdos821.S34Core

open Blueprint.Analytic

alias norm_e := _root_.Erdos821.P4Rat.rf_e_norm

theorem rational_phase_split  n θ β ζ  (u : ℤ) (r : ℕ)
    (hn : 0 < n) (hθ : θ = (u : ℝ) / r + β) :
    mellin n ζ * e (θ * n) = logMultiplier ζ β (Real.log n) * e ((u : ℝ) * n / r) := by
  unfold Blueprint.Analytic.mellin e logMultiplier unitPhase
  rw [Real.exp_log hn, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hθ]
  push_cast
  ring


end Erdos821.S34Core
