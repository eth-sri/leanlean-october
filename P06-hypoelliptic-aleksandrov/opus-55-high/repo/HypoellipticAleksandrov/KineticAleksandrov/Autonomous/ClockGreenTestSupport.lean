module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTest

/-! # Compact clock tests have a genuine late cutoff -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- A compact physical probe has a strictly positive cutoff above its entire time support. -/
theorem clock_probe_cutoff (f : exitProbeSubmodule) :
    ∃ R : ℝ, 0 < R ∧
      (∀ p ∈ tsupport (exitProbePhysical f), p.time < R) ∧
      (∀ p, R ≤ p.time → exitProbePhysical f p = 0) := by
  have hc := (exitProbePhysical_continuous_compact f).2
  obtain ⟨b, hb⟩ := (hc.image continuous_time).bddAbove
  refine ⟨max b 0 + 1, by positivity, ?_, ?_⟩
  · intro p hp
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hp, rfl⟩)
    grind
  · intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hs, rfl⟩)
    grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
