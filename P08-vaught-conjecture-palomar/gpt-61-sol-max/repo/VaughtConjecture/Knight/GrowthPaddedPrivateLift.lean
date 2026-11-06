
import VaughtConjecture.Knight.PointwiseLabels

import VaughtConjecture.Knight.MapRestoration
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedPrivateRepair
import VaughtConjecture.Knight.GradeSplice
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import VaughtConjecture.Knight.WitnessSplice

/-! # Active positive-cap private lifting on the unchanged padded successor

Literal restoration uses the already-proved grade-one scope-raising lift.
The successor's bountifulness is neither assumed nor claimed here.
Adapted from `LowOnlyPaddedPrivateLift`; the predecessor lift and source fibre
are growth theorems, not LOW-family substitutions.
-/

namespace VaughtConjecture.Knight.GrowthPaddedPrivateLift
open    CappedDonor Growth
open GrowthPaddedSuccessor GrowthPaddedDecode GrowthPaddedCharts GrowthPaddedPrivateRepair
open GradeTailRestoration AmalgamationPlan


variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows I X T hA hB hC) (A, 2)

local notation "carrier₀" => carrier I X T hA hB hC

local notation "privateAt₀" => privateAt I X T hA hB hC

/-- Restore the entire private lower vector using the unchanged padded base.
Every lower auxiliary retains its owner cap; every upper locality target stays
unchanged. This is a proved restoration, not an input to the final endpoint. -/
theorem restore
    {p}
    {u}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hu : RespectsSemanticsBelow₀ u)
    {M} (hM : SelfVis 2 M)
    (hread : ∀ d, u (privateAt₀ d) = min (p d) M)
    (hbound : BoundedBy u M)
    (hmax : ∀ d, I.right.scheme.grade d.1 = 2 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ privateAt₀) p) ∧
      CappedEq r u M := by
  let e := lowerEquiv I X T hA hB hC
  let inc := CellScheme.below.mono (D := I.right.scheme)
    (show GradedLe (Finset.univ, 1) (Finset.univ, 2) from
      ⟨Finset.Subset.refl _, by omega⟩)
  refine restore_map (by omega) e (lower_respects_iff)
    inc (privateAt₀) (GrowthOrderedBase.privateAt I X (by omega)) (fun _ => rfl) ?_ hu hread hbound ?_ ?_
  · intro d hd
    have hd' : I.right.scheme.grade d.1 ≤ 1 := by
      simpa only [private_grade] using hd
    exact ⟨⟨d.1, Finset.subset_univ _, hd'⟩, rfl⟩
  · intro d hd
    apply hmax d
    have hb : I.right.scheme.grade d.1 ≤ 2 := d.2.2
    simp only [private_grade] at hd
    omega
  · intro q hq hcap
    exact GrowthOrderedBase.private_lift I X T
      (by omega) hB hC (hp.mono (show GradedLe (Finset.univ, 1) (Finset.univ, 2) from
        ⟨Finset.Subset.refl _, by omega⟩)) hq
      (hM.mono (by decide : 1 ≤ 2)) hcap

/-- Arbitrary lawful private prescription and target-local ambient, with an
active prescribed grade-two value. The maximal owner, chart, source-cut
prescription, admitted repair, and lower restoration are all constructed.
Every physical auxiliary has its own original-cap receipt, including unused
rungs and the long tips. Literal top is not excluded. -/
theorem active_private_lift
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 2) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis 2 γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.right.scheme.grade d.1 = 2 ∧ γ < p d)
    (hag : CappedEq (q ∘ privateAt₀) p γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (PointwiseEq (r ∘ privateAt₀) p) ∧
      CappedEq r q γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn  := by simpa only [hd] using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.right.complete (Finset.univ, 2)
    (Plan.mem_gradedPlan.mpr ⟨I.right.scheme.isPlan.domain_mem, by omega,
      by simp_all⟩)
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      hc₀⟩
  have hg : I.right.scheme.grade c.1 = 2 := congrArg Prod.snd hc
  have hci  := hc
  have hpc  := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped I X T hA hB hC c hci hg hp hq hγ hpos hpc hag
  have hM  := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := restore I X T hA hB hC hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩


