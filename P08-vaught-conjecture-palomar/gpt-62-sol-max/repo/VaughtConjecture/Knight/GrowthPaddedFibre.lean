/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedNativeFace
public import VaughtConjecture.Knight.GrowthPaddedIteration

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedFibre

open Transform Value ExtOrd Padded CappedDonor Growth GrowthOrderedBase GrowthPaddedContract

open AmalgamationPlan CoatomBoundaryExtension GrowthPaddedIteration

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : BuildContext A B C R m n J)

local notation "GrowthSpec" => spec G.I G.X G.attach G.height G.leftProper G.rightProper

theorem privateNative : NativeFace (K := GrowthSpec) G.I.rightFace id where
  le_cutoff _ := le_rfl
  monotone := monotone_id
  grade_cut _ _ h := h
  fibre hj _ := (G.attach.private_fibre hj).reindex (fun _ hs d => (GrowthOrderedBase.field_private G.I G.X G.attach hs d.1).symm)

theorem donorNative (hsmall : n + 1 < G.X.req.N) : NativeFace (K := GrowthSpec) G.I.leftFace id where
  le_cutoff _ := le_rfl
  monotone := monotone_id
  grade_cut _ _ h := h
  fibre hj h := by
    obtain ⟨d, hd⟩ := h
    exact (G.attach.donor_fibre hj (hd ▸ Growth.donor_grade_lt G.I.left hsmall d.1)).reindex (fun s _ d => (GrowthOrderedBase.field_donor G.I s d.1).symm)

/-- First use the literal original face's lifting clauses, then the native installed fibre. -/
theorem subface (hsmall : n + 1 < G.X.req.N) {S : Finset ι} {i j : ℕ}
    (hS : (S, i) ∈ Plan.gradedPlan R) (hs : S ⊆ B ∨ S ⊆ C) (hij : i ≤ j) (hj : j ≤ G.depth + 2) :
    CappedLift G.tower.rows (show GradedLe (S, i) (A, j) from
      ⟨G.I.isPlan.subset_of_mem (Plan.mem_gradedPlan.mp hS).1, hij⟩) :=
  G.I.subface_to_full G.donorFace G.privateFace G.leftProper.subset G.rightProper.subset hS hs hij
    (fun h => (donorNative G hsmall).capped_clause G.I.consistent G.leftProper G.depth G.fits
      (Plan.mem_gradedPlan.mp h).2.1 (hij.trans hj))
    (fun h => (privateNative G).capped_clause G.I.consistent G.rightProper G.depth G.fits
      (Plan.mem_gradedPlan.mp h).2.1 (hij.trans hj))

end

end VaughtConjecture.Knight.GrowthPaddedFibre
