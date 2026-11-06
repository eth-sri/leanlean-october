module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardValue

/-! # The weighted clock identity for the actual infinite physical Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/- The advancing-clock cone holds on the actual infinite physical Green measure. -/
theorem clock_forward_cone_infinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : StripPole c.activeInterval ⊤) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤ e,
      p.time - e.1.time ≤ 2 * c.r ^ 2 * (c.map e.1 p).time := by
  apply stripGreen_infinite_ae_of_finite hH hLE hlam hLam A c.activeInterval e
  intro T ht
  exact (clock_forward_cone_finite hH hLE hlam hLam A c T
    (stripPoleFinite c.activeInterval e T ht)).2

/- Compact nonnegative normalized interior tests satisfy the genuine infinite weighted identity. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
