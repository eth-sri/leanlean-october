module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardTests
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport

/-! # Actual clock Duhamel values equal the normalized infinite Green test integral -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/- The physical normalized initial pole has time and transported coordinate zero. -/
def clockPhysicalPole (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    StripPole clockNormalizedInterval ⊤ :=
  ⟨⟨0, fun _ => 0, fun _ => (e.velocity 0 - c.vbar) / c.r⟩,
    WithTop.coe_lt_top _, (c.mem_active_iff (e.velocity 0)).mp he⟩

/- The literal position clock sends its source pole to the normalized initial pole. -/
theorem clockGreen_eq_stripGreenOfKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    clockGreen hH hLE hlam hLam A c e he =
      stripGreenOfKernel clockNormalizedInterval (clockEvolution hH hLE hlam hLam A c e).2
        ⊤ (clockPhysicalPole c e he) := rfl

/- Late vanishing identifies the genuine clock test value with the actual infinite Green
  integral. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
