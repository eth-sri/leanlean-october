
import VaughtConjecture.Knight.PointwiseLabels

import VaughtConjecture.Knight.MapRestoration
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedDonorRepair
import VaughtConjecture.Knight.GradeSplice
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import VaughtConjecture.Knight.WitnessSplice

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the already-proved grade-one scope-raising lift.
The successor's bountifulness is neither assumed nor claimed here.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedDonorLift
open    CappedDonor LowOnly
open LowOnlyPaddedSuccessor LowOnlyPaddedDecode LowOnlyPaddedCharts LowOnlyPaddedDonorRepair
open GradeTailRestoration


variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2)

local notation "carrier₀" => carrier I F hroot hA hB hC

local notation "donorAt₀" => donorAt I F hroot hA hB hC

/-- Restore the entire donor lower vector using the unchanged padded base.
Every lower auxiliary retains its owner cap; every upper locality target stays
unchanged. This is a proved restoration, not an input to the final endpoint. -/
theorem restore
    {p}
    {u}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hu : RespectsSemanticsBelow₀ u)
    {M} (hM : SelfVis 2 M)
    (hread : ∀ d, u (donorAt₀ d) = min (p d) M)
    (hbound : BoundedBy u M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = 2 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ donorAt₀) p) ∧
      CappedEq r u M := by
  let e := lowerEquiv I F hroot hA hB hC
  let inc := CellScheme.below.mono (D := I.left.scheme)
    (CappedDonor.Ref.effC_mono (by decide : 1 ≤ 2))
  refine restore_map (by omega) e (lower_respects_iff)
    inc (donorAt₀) (Family.donorAt F I.boundary (by omega) (LowOnlyOrderedLadder.donorIncl I)) (fun _ => rfl) ?_ hu hread hbound ?_ ?_
  · intro d hd
    have hd' : I.left.scheme.grade d.1 ≤ 1 := by
      simpa only [donor_grade] using hd
    exact ⟨⟨d.1, Finset.subset_univ _, le_min hd' (gradeC_le d.1)⟩, rfl⟩
  · intro d hd
    apply hmax d
    have hb : I.left.scheme.grade d.1 ≤ 2 := d.2.2.trans (min_le_left 2 n)
    simp only [donor_grade] at hd
    omega
  · intro q hq hcap
    exact LowOnlyOrderedLadder.donor_lift I F hroot
      (by omega) hB hC (hp.mono (CappedDonor.Ref.effC_mono (by decide))) hq
      (hM.mono (by decide)) hcap

/-- Arbitrary lawful donor prescription and target-local ambient, with an
active prescribed grade-two value. The maximal owner, chart, source-cut
prescription, admitted repair, and lower restoration are all constructed.
Every physical auxiliary has its own original-cap receipt, including unused
rungs and the long tips. Literal top is not excluded. -/
theorem active_donor_lift
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 2) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = 2 ∧ γ < p d)
    (hag : CappedEq (q ∘ donorAt₀) p γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ donorAt₀) p) ∧
      CappedEq r q γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn  := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (effC n 2)
    (CappedDonor.effC_mem (by decide) (by omega))
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer (k := 2) hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      by simp_all only [effC] <;> aesop⟩
  have hg : I.left.scheme.grade c.1 = 2 := congrArg Prod.snd hc
  have hci : I.left.scheme.cell c.1 = effC n 2 := by
    simp_all [effC]
  have hpc  := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped I F hroot hA hB hC c hci hg hp hq hγ hpos hpc hag
  have hM  := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := restore I F hroot hA hB hC hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩


