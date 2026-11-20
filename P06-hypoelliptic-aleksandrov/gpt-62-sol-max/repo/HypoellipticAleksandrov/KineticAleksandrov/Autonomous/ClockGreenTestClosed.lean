module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforwardCone

/-! # The clock carries the actual physical closed strip to the normalized closed strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The literal clock maps the closed physical active interval to the normalized closed interval. -/
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

section
variable {lam Lam : ℝ} {A : SmoothAutonomous lam Lam} {c : Clock} {e : Point} {R T : ℝ}
  {f : exitProbeSubmodule} (h : ClockSourcePotentialSpec A c e R T f)
include R h

/-- Actual normalized Duhamel boundary continuity transfers to the entire physical closed strip. -/
theorem ClockSourcePotentialSpec.pullback_continuous :
    ContinuousOn
      ((clockSourcePotential A c e T f ∘ sectionTwoPoint) ∘ c.map e)
      {p | p.velocity 0 ∈ Icc c.activeInterval.lo c.activeInterval.hi} := by
  apply h.continuous_closed.comp ((continuous_sectionTwoPoint 1).comp (c.homeomorph e).continuous).continuousOn
  intro p hp
  exact c.closed_active_image e p hp

/-- Each physical lateral face maps to its matching actual normalized Dirichlet face. -/
theorem ClockSourcePotentialSpec.pullback_zero_faces
    (p : Point) (hp : p.velocity 0 = c.activeInterval.lo ∨
      p.velocity 0 = c.activeInterval.hi) :
    clockSourcePotential A c e T f (sectionTwoPoint (c.map e p)) = 0 := by
  apply h.lateral_zero
  change (p.velocity 0 - c.vbar) / c.r = -3 / 4 ∨
    (p.velocity 0 - c.vbar) / c.r = 3 / 4
  rcases hp with hp | hp
  · left
    rw [hp]
    dsimp [Clock.activeInterval]
    field_simp [ne_of_gt c.positive]
    ring
  · right
    rw [hp]
    dsimp [Clock.activeInterval]
    field_simp [ne_of_gt c.positive]
    ring

end

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
