
import VaughtConjecture.Knight.PointwiseLabels

import VaughtConjecture.Knight.MapRestoration
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthPaddedStepDonorRepair
import VaughtConjecture.Knight.GrowthPaddedOriginalLifts
import VaughtConjecture.Knight.GradeSplice
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import VaughtConjecture.Knight.WitnessSplice

/-! # Active positive-cap donor lifting on the unchanged padded successor

Literal restoration uses the previously proved original-face lift.
The concrete grade-three endpoint discharges the lower input using the
checked all-cap grade-two theorem. No output bountifulness is assumed.
Adapted from `LowOnlyPaddedPrivateLift`; the predecessor lift and source fibre
are growth theorems, not LOW-family substitutions.
-/

namespace VaughtConjecture.Knight.GrowthPaddedStepDonorLift
open    CappedDonor Growth
open GrowthPaddedContract GrowthPaddedStepRows GrowthPaddedStepDecode
open GrowthPaddedStepDonorRepair
open GradeTailRestoration AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {T : I.GrowthAttachment X}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I X T hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

/-- The previous donor face, on the actual predecessor. -/
def previousDonorAt (d : I.left.scheme.below (Finset.univ, k)) :
    P.carrier.below (A, k) :=
  ⟨P.baseMap (RelativeLadderLayer.old I.boundary (by omega) (I.leftFace.map d.1)), by
    rw [P.base_index, RelativeLadderLayer.old_index]
    exact ⟨I.boundary.scope_subset _,
      (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩⟩

local notation "RespectsSemanticsBelow₀₀" => RespectsSemanticsBelow P.rows (A, k)

/-- Only the predecessor's original-donor lift is needed for restoration. -/
def DonorLowerLift :=
  ∀ p
    q γ,
    RespectsSemanticsBelow I.left.rows (Finset.univ, k) p →
    RespectsSemanticsBelow₀₀ q → SelfVis k γ →
    (∀ d, min (q (previousDonorAt P d)) γ = min (p d) γ) →
    ∃ r, RespectsSemanticsBelow₀₀ r ∧
      (∀ d, r (previousDonorAt P d) = p d) ∧
      ∀ d, min (r d) γ = min (q d) γ

def lowerEquiv : P.carrier.below (A, k) ≃ (carrier P hnext).below (A, k) :=
  HighLayerBountiful.equiv P.carrier (Catalogue X (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (A, k) (fun h => by have := h.2; omega)

theorem lower_respects_iff p :
    RespectsSemanticsBelow₀₀ p ↔
      RespectsSemanticsBelow (rows P hk hnext) (A, k)
        (p ∘ (lowerEquiv P hnext).symm) := by
  apply respects_iff_of_equiv (lowerEquiv P hnext)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _)).symm)
    (fun d e => ?_) (fun b d _ => ?_) p
  · simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell]
  · exact (inherited_row P hk hnext b.1 d).symm

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)

/-- Restore the entire donor lower vector using the actual predecessor.
Every lower auxiliary retains its owner cap; every upper locality target stays
unchanged. This is a proved restoration, not an input to the final endpoint. -/
theorem restore (hprev : DonorLowerLift P)
    {p}
    {u}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hu : RespectsSemanticsBelow₀ u)
    {M} (hM : SelfVis (k + 1) M)
    (hread : ∀ d, u (donorAt P hnext d) = min (p d) M)
    (hbound : BoundedBy u M)
    (hmax : ∀ d, I.left.scheme.grade d.1 = k + 1 → p d ≤ M) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      CappedEq r u M := by
  let e := lowerEquiv P hnext
  let inc := CellScheme.below.mono (D := I.left.scheme)
    (show GradedLe (Finset.univ, k) (Finset.univ, k + 1) from
      ⟨Finset.Subset.refl _, by omega⟩)
  refine restore_map (by omega) e (lower_respects_iff P hk hnext)
    inc (donorAt P hnext) (previousDonorAt P) (fun _ => rfl) ?_ hu hread hbound ?_ ?_
  · intro d hd
    have hd' : I.left.scheme.grade d.1 ≤ k := by
      simpa only [donor_grade] using hd
    exact ⟨⟨d.1, Finset.subset_univ _, hd'⟩, rfl⟩
  · intro d hd
    apply hmax d
    have hb : I.left.scheme.grade d.1 ≤ k + 1 := d.2.2
    simp  [donor_grade] at hd
    omega
  · intro q hq hcap
    exact hprev _ _ M
      (hp.mono (show GradedLe (Finset.univ, k) (Finset.univ, k + 1) from
        ⟨Finset.Subset.refl _, by omega⟩)) hq
      (hM.mono (by omega)) hcap

/-- Arbitrary lawful donor prescription and target-local ambient, with an
active prescribed current-grade value. The maximal owner, chart, source-cut
prescription, admitted repair, and lower restoration are all constructed.
Every physical auxiliary has its own original-cap receipt, including unused
rungs and the long tips. Literal top is not excluded. -/
theorem active_donor_lift (hN : k + 1 < X.req.N) (hprev : DonorLowerLift P)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, k + 1) p)
    (hq : RespectsSemanticsBelow₀ q)
    {γ} (hγ : SelfVis (k + 1) γ) (hpos : ⊥ < γ)
    (hactive : ∃ d, I.left.scheme.grade d.1 = k + 1 ∧ γ < p d)
    (hag : ∀ d, min (q (donorAt P hnext d)) γ = min (p d) γ) :
    ∃ r, RespectsSemanticsBelow₀ r ∧
      (∀ d, r (donorAt P hnext d) = p d) ∧
      CappedEq r q γ := by
  obtain ⟨d, hd, hpd⟩ := hactive
  have hn  := by simpa only  using gradeC_le d.1
  obtain ⟨c₀, hc₀⟩ := I.left.complete (Finset.univ, k + 1)
    (Plan.mem_gradedPlan.mpr ⟨I.left.scheme.isPlan.domain_mem, by omega,
      by simp_all⟩)
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩,
      hc₀⟩
  have hg : I.left.scheme.grade c.1 = k + 1 := congrArg Prod.snd hc
  have hci  := hc
  have hpc  := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ :=
    owner_capped P hk hnext hN c hci hg hp hq hγ hpos hpc hag
  have hM  := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := restore P hk hnext hprev hp hu hM hread hbound hmax
  exact ⟨r, hr, hrr, fun e => (cap_below (hrc e) hpc.le).trans (hcap e)⟩

variable (I X T hA hB hC)

