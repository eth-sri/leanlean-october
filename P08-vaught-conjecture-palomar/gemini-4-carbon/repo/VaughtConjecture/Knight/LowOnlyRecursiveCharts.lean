/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveRungLocality
public import VaughtConjecture.Knight.LowOnlyLadderRepair

/-! # Recursive auxiliary charts for the actual LOW catalogues

Every source grade uses its own finite admitted catalogue. Canonical membership
supplies properness, bounds and native shortness; present-cell lawfulness and
future visibility supply grade-one visibility on the complete field vector.
Thus the recursive charts specialize without an abstract source-row contract.

This is numerical auxiliary locality, not original-owner lawfulness or an
installed scope geometry. It neither promotes admission to a higher cutoff nor
asserts equality of renderings made at different construction grades.
-/

@[expose] public section

set_option autoImplicit false
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
  · exact hf d (Nat.lt_of_not_ge hd)

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

theorem anchor_short {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    Short j (F.fields j a d) :=
  CanonicalPairedProfiles.inventory_short _ _ a.property.1 d

theorem anchor_visible_one {j : ℕ} (hj : 1 ≤ j) (a : F.Anchor j) (d : Field P C) :
    SelfVis 1 (F.fields j a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d)
  rw [← he]
  exact profile_visible_one F hj hS d

end
end VaughtConjecture.Knight.LowOnlyRecursiveCharts
