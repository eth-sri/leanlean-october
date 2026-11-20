/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveRungRendering
public import VaughtConjecture.Knight.LowOnlyLadderRepair

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyRecursiveCharts

open Transform Value ExtOrd CappedDonor LowOnly

open PairedSlotEncoding RecursiveRungRendering

open SharpWitnessComposition

noncomputable section

variable {m K : ℕ} {P C : SemScheme m} (F : LowOnly.Family P C K)

private theorem lower_visible_one {D : SemScheme m} {j : ℕ}
    {v : Cell D.scheme → ExtOrd}
    (hv : RespectsSemanticsBelow D.rows (effC m j) (fun d => v d.1))
    (hf : ∀ d, j < D.scheme.grade d → SelfVis 1 (v d)) (d : Cell D.scheme) :
    SelfVis 1 (v d) := by
  by_cases hd : D.scheme.grade d ≤ j
  · let d' : D.scheme.below (effC m j) :=
      ⟨d, Finset.subset_univ _, le_min hd (gradeC_le d)⟩
    exact selfVis_mono (hv.orderly d').symm (D.scheme.grade_pos d)
  grind

/-- Future fields and the free cutoff are covered too. -/
theorem profile_visible_one {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (d : Field P C) : SelfVis 1 (S.profile d) := by
  rcases d with d | d | d
  · exact lower_visible_one hS.lawfulP hS.futureP d
  · exact lower_visible_one hS.lawfulC hS.futureC d
  · exact selfVis_mono hS.cutoff (le_min hj F.gap.K_pos)

theorem anchor_proper {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≠ ⊤ := a.property.1.2 d

theorem anchor_bound {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≤ ceiling (Field P C) j := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 d).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

end

end VaughtConjecture.Knight.LowOnlyRecursiveCharts
