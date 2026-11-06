module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestClosed

/-! # Actual uniform-in-spacetime bounds for a physical clock test -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/- The genuine clock potential and its literal physical source are bounded on the active strip. -/
theorem clock_C112_mono {u : Point → ℝ} {D E : Set Point}
    (hu : IsKineticC112On u D) (hi : E ⊆ D) : IsKineticC112On u E :=
  ⟨hu.1.mono hi, fun p hp => hu.2.1 p (hi hp),
    fun p hp => hu.2.2.1 p (hi hp), fun p hp => hu.2.2.2.1 p (hi hp),
    hu.2.2.2.2.1.mono hi, hu.2.2.2.2.2.1.mono hi,
    hu.2.2.2.2.2.2.1.mono hi, hu.2.2.2.2.2.2.2.mono hi⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
