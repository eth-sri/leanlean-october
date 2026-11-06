module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport

/-! # Open strip and terminal/lateral exit for homogeneous reconstruction

The initial time is absent from the regularity set. Endpoint identities require a
strictly larger regularity strip, as the endpoint convention requires.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The physical finite strip, open at both time endpoints. -/
def reconstructionStrip (H : Interval) (sMinus T : ℝ) : Set Point :=
  {p | sMinus < p.time ∧ p.time < T ∧ p.velocity 0 ∈ H.carrier}

/-- The prescribed exit omits the initial velocity face. -/
def reconstructionExit (H : Interval) (sMinus T : ℝ) : Set Point :=
  {p | p.time = T ∧ p.velocity 0 ∈ Set.Icc H.lo H.hi} ∪
    {p | sMinus < p.time ∧ p.time < T ∧
      (p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi)}

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
