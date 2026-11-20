/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedPairLift
public import VaughtConjecture.Knight.CappedLiftComposition

/-! # Closed all-cap lifting induction on the installed padded tower

The actual grade-two base initializes the uniform successor ledger. Every
predecessor lifting input is discharged by induction on integration's unchanged
build. Completeness is restricted to installed heights; the ambient-height
output is bountiful and complete.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedContract PaddedTower.Step LowOnlyOrderedLadder
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)
  (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

open LowOnlyPaddedIteration AmalgamationPlan CoatomBoundaryExtension
include hcover

/-- Completeness is asserted only at filled grades. Proper original owners
above this height are retained but no missing full owners are postulated. -/
theorem complete_through t (ht : t + 2 ≤ A.card) {J}
    (hJ : J ∈ Plan.gradedPlan R) (hj : J.2 ≤ t + 2) :
    ∃ d, (build frame t ht).carrier.cell d = J := by
  let L := build frame t ht
  rcases J with ⟨T, j⟩
  by_cases he : T = A
  · subst T
    exact L.occupied j (Plan.mem_gradedPlan.mp hJ).2.1 hj
  · obtain ⟨d, hd⟩ := (I.occupied_iff hJ).mpr (hcover T (Plan.mem_gradedPlan.mp hJ).1 he)
    refine ⟨L.baseMap (RelativeLadderLayer.old I.boundary frame.positive d), ?_⟩
    exact (L.base_index _).trans
      ((RelativeLadderLayer.old_index I.boundary frame.positive d).trans hd)

/-- At the ambient height every permitted graded pair is covered. -/
theorem full_bountiful :
    (build frame (A.card - 2) frame.fullHeight.le).rows.IsBountiful := by
  intro U V hU hV h _
  have hv : V.2 ≤ A.card - 2 + 2 := by
    have hV' := Plan.mem_gradedPlan.mp hV
    have hscope :=
      (build frame (A.card - 2) frame.fullHeight.le).carrier.isPlan.subset_of_mem hV'.1
    have hb := hV'.2.2.trans (Finset.card_le_card hscope)
    omega
  let L := build frame (A.card - 2) frame.fullHeight.le
  have hu : U ∈ Plan.gradedPlan R := by rwa [build_plan] at hU
  have hv' : V ∈ Plan.gradedPlan R := by rwa [build_plan] at hV
  have mem : (V.1,U.2) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
    ⟨(Plan.mem_gradedPlan.mp hv').1, (Plan.mem_gradedPlan.mp hu).2.1, h.2.trans (Plan.mem_gradedPlan.mp hv').2.2⟩
  obtain ⟨S,i⟩ := U
  exact (I.liftViaFaces (L.face I.leftFace frame.leftProper.not_ge) (L.face I.rightFace frame.rightProper.not_ge)
    frame.leftProper.subset frame.rightProper.subset hcover
    (fun hn => LowOnlyPaddedPairLift.donor_clause frame _ _ (Plan.mem_gradedPlan.mp hu).2.1 hn (h.2.trans hv))
    (fun hn => LowOnlyPaddedPairLift.private_clause frame _ _ (Plan.mem_gradedPlan.mp hu).2.1 hn (h.2.trans hv)) hu mem h.1).raise_target (h := h.1) h.2

theorem full_complete :
    (build frame (A.card - 2) frame.fullHeight.le).carrier.IsComplete := by
  intro J hJ
  have hJ' := Plan.mem_gradedPlan.mp hJ
  have hscope :=
    (build frame (A.card - 2) frame.fullHeight.le).carrier.isPlan.subset_of_mem hJ'.1
  have hb := hJ'.2.2.trans (Finset.card_le_card hscope)
  apply complete_through frame hcover (A.card - 2) frame.fullHeight.le _ (by omega)
  rwa [build_plan] at hJ

end
end VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
