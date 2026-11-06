module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardCone

/-! # The clock carries the actual physical closed strip to the normalized closed strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/- The literal clock maps the closed physical active interval to the normalized closed interval. -/
theorem Clock.closed_active_image (c : Clock) (e p : Point)
    (hp : p.velocity 0 ∈ Icc c.activeInterval.lo c.activeInterval.hi) :
    (sectionTwoPoint (c.map e p)).position ∈ closure (intervalDomain clockNormalizedInterval) := by
  apply (nested_intervalDomain_closure_iff clockNormalizedInterval _).mpr
  change -3 / 4 ≤ (p.velocity 0 - c.vbar) / c.r ∧
    (p.velocity 0 - c.vbar) / c.r ≤ 3 / 4
  constructor
  · apply (le_div_iff₀ c.positive).mpr
    have hh : c.vbar - 3 * c.r / 4 ≤ p.velocity 0 := hp.1
    linarith
  · apply (div_le_iff₀ c.positive).mpr
    have hh : p.velocity 0 ≤ c.vbar + 3 * c.r / 4 := hp.2
    linarith

/- Actual normalized Duhamel boundary continuity transfers to the entire physical closed strip. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
