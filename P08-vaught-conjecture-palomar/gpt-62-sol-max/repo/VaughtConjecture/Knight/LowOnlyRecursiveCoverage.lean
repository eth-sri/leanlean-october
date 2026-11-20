/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyRecursiveCharts

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyRecursiveCoverage

open Transform Value ExtOrd CappedDonor LowOnly

open PairedSlotEncoding PairedSlotComparison RecursiveRungRendering

open LowOnlyRecursiveCharts

noncomputable section

variable {m K : ℕ} {P C : SemScheme m} (F : LowOnly.Family P C K)

/-- The same complete state is admitted at every lower cutoff. Crossing fields
are one-visible by their old lawfulness, not by a new source-family assumption. -/
theorem admissible_down {i j : ℕ} (hj : 1 ≤ j) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) : F.Admissible i S where
  lawfulP := hS.lawfulP.mono (CappedDonor.Ref.effC_mono hij)
  lawfulC := hS.lawfulC.mono (CappedDonor.Ref.effC_mono hij)
  shared := hS.shared
  futureP d _ := profile_visible_one F hj hS (.inl d)
  futureC d _ := profile_visible_one F hj hS (.inr (.inl d))
  cutoff := selfVis_mono hS.cutoff (min_le_min_right K hij)
  low hKi hm d hd := hS.low (hKi.trans hij) hm d hd

/-- Canonical normalization at a lower grade lands in the existing catalogue. -/
def normalizedAnchor {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) : F.Anchor i :=
  ⟨(S.normalize i).profile, LowOnly.Family.normalize_inventory i hp,
    S.normalize i, F.normalize_admissible hi (admissible_down F (hi.trans hij) hij hS), rfl⟩

end

end VaughtConjecture.Knight.LowOnlyRecursiveCoverage
