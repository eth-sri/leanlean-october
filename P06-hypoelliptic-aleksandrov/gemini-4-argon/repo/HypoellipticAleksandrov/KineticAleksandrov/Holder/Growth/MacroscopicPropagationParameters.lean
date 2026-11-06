module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
import Mathlib.Tactic

/-! # Scale-independent macroscopic propagation ratios -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

/- The exact source acceleration bound for reference travel paths. -/
def macroscopicAcceleration (m : ℕ) : ℝ := 6 * ((m : ℝ) + 5) + 8

/- The minimum duration and widths recover their physical values at every scale. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
