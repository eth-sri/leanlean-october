module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTest

/-! # Compact clock tests have a genuine late cutoff -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous



/-- A compact physical probe has a strictly positive cutoff above its entire time support. -/
theorem clock_probe_cutoff (f : exitProbeSubmodule) :
    ∃ R : ℝ, 0 < R ∧
      (∀ p ∈ tsupport (exitProbePhysical f), p.time < R) ∧
      (∀ p, R ≤ p.time → exitProbePhysical f p = 0) := by

  obtain ⟨b, hb⟩ := (((exitProbePhysical_continuous_compact f).2).image continuous_time).bddAbove
  refine ⟨max b 0 + 1, by have := le_max_right b 0; linarith, ?_, ?_⟩
  · intro p hp
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hp, rfl⟩)
    have := le_max_left b 0
    linarith
  · intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have ht := hb (show p.time ∈ KineticPoint.time '' tsupport (exitProbePhysical f)
      from ⟨p, hs, rfl⟩)
    have := le_max_left b 0
    linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
