module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1FourierMoments
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Raw position-frequency scaling before any probability normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory

/- The structural stretched-exponential moment at unit spatial scale. -/
def exitFrequencyMoment {d : ℕ} (c : ℝ) (j : ℕ) : ℝ :=
  ∫ ξ : PDE.Vec d, ‖ξ‖ ^ j * Real.exp (-c * ‖ξ‖ ^ (1 / 3 : ℝ))

/- Unit-scale frequency moments are nonnegative. -/
theorem exitFrequencyMoment_nonneg {d } (c : ℝ) (j : ℕ) :
    0 ≤ exitFrequencyMoment (d := d) c j :=
  integral_nonneg (fun ξ => mul_nonneg (pow_nonneg (norm_nonneg ξ) j) (Real.exp_pos _).le)

/- Frequency dilation gives the raw dimension-plus-derivative scaling factor. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
