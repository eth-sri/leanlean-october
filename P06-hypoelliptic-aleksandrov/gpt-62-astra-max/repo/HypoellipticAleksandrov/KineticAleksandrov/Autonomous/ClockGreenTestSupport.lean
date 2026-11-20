module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTest

/-! # Compact clock tests have a genuine late cutoff -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- A compact physical probe has a strictly positive cutoff above its entire time support. -/
theorem clock_probe_cutoff (f : exitProbeSubmodule) :
    ∃ R : ℝ, 0 < R ∧
      (∀ p ∈ tsupport (exitProbePhysical f), p.time < R) ∧
      (∀ p, R ≤ p.time → exitProbePhysical f p = 0) := by
  obtain ⟨b, hb⟩ := (((exitProbePhysical_continuous_compact f).2).image continuous_time).bddAbove
  refine ⟨max b 0 + 1, by linarith [le_max_right b 0], ?_, ?_⟩
  · intro p hp
    have ht := hb (⟨p, hp, rfl⟩)
    linarith [le_max_left b 0]
  · intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have ht := hb (⟨p, hs, rfl⟩)
    linarith [le_max_left b 0]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
