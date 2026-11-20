/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SmallCoatomSeeds

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalCoatomSupply

open Transform Value ExtOrd AmalgamationPlan SemSchemeBoundaryInput

noncomputable section

private theorem install {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) {n : ℕ}
    (C : CoatomPair n) {pa pb : S α (n + 1)} (h : C.Compatible pa pb)
    (seed : CoatomSeedInstallation.Seed (CoatomBoundaryPresentation.of_compatible C h).input) :
    ∃ t : S α (n + 2), C.IsAmalgam pa pb t ∧ t.HasMaximalFullCell := by
  obtain ⟨t, hl, hr, hm⟩ := CoatomSeedInstallation.install _ seed
    hα pa.respects pb.respects pa.label_bound pb.label_bound
    (CoatomBoundaryPresentation.compatible_labels C h)
  tauto

/-- The finite supplier, with no completion or lifting assumptions on an output. -/
theorem supply {α : Ordinal.{0}} (hα : Order.IsSuccLimit α) :
    MaximalCoatomAmalgamationSupply α := by
  intro n C pa pb h
  rcases n with _ | _ | n
  · exact install hα C h (SmallCoatomSeeds.one _)
  · exact install hα C h (SmallCoatomSeeds.two _)
  · exact CoatomRecursiveOrdered.exists_amalgam hα C h

end

end VaughtConjecture.Knight.CanonicalCoatomSupply
