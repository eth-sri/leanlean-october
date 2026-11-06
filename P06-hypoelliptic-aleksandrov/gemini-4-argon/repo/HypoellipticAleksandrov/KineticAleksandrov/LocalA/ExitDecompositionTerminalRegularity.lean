module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDecompositionComparison
import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW

/-! # Restriction of genuine terminal solutions to physical local strips -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic TheoremA

/- Swapping physical coordinates maps the local closed strip into the past closed cylinder. -/
theorem exit_closed_into_past {d a T R v₀}
    {Q : KineticPoint d} (hQ : Q ∈ localClosedStrip a T v₀ R) :
    sectionTwoPoint Q ∈ evolutionPastClosedCylinder (PDE.euclideanBall v₀ R)
      (fun _ => 0) T :=  ⟨hQ.2.1, by simpa only [sectionTwoPoint, movingDomain_ball_zero] using hQ.2.2⟩

/- Swapping physical coordinates maps the open strip into the genuine past interior. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
