
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.RankRepair

import VaughtConjecture.Knight.LowOnlyDonorGradeOneSource
import VaughtConjecture.Knight.LowOnlyGradeOneLift

/-! # Positive-cap donor lifting on the unchanged padded LOW ladder

Attribution: the physical rank-table endgame is the donor-occurrence
specialization of `LowOnlyGradeOneLift`. It reuses the actual capped leaf chart,
rank-table interpolation, rank decoder and raw-row lawfulness. Admission is
constructed by the donor release fibre, not a symmetry of LOW.
-/

namespace VaughtConjecture.Knight.LowOnly.Family
open    CappedDonor 
open LadderScalarRendering SharpWitnessComposition RelativeLadderLayer
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : AvoidsValue D.scope A)
  (hboundary : ∀ S , F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))
  (incl : P.scheme.below (effC n 1) → D.below (A, 1))
  (hfield : ∀ S, F.Admissible 1 S → ∀ d,
    S.profile (field (incl d).1) = S.u d.1)

local notation "L" => carrier D hA (X := Field P C) (Q := F.Anchor 1)
local notation "E" => rows D sem hA field (F.fields 1) hproper
local notation "H" => rungs (X := Field P C)
local notation "below₀" => P.scheme.below (effC n 1)

local instance donorLiftFintype : Fintype (below₀) := Fintype.ofFinite _

def donorAt (d : below₀) : (L).below (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

include hfield in
theorem anchor_donor (a : F.Anchor 1) (d : below₀) :
    F.fields 1 a (field (incl d).1) = a.val (.inl d.1) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change a.val (field (incl d).1) = a.val (.inl d.1)
  rw [← he]
  exact hfield S hs d

local notation "donorAt₀" => donorAt F D hA incl

local notation "leafSource₀" => leafSource F D hA field

include hfield in
theorem leafSource_donor (a : F.Anchor 1) (d : below₀) :
    leafSource₀ a (donorAt₀ d).1 =
      SupportLadderRows.source H (fieldRank a.val (.inl d.1)) := by
  simp  [leafSource, donorAt, image,  ranks, fieldRank,
    anchor_donor F D field incl hfield a d]
  rfl

include hboundary hfield in
/-- Arbitrary-input active lifting. All replacement/source data are constructed;
the hypotheses describe only the original boundary and the actual input query. -/
theorem donor_active_lift
    {p : below₀ → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : CappedEq (q ∘ donorAt₀) p γ)
    (c : below₀) (hactive : γ < p c) :
    ∃ w , RespectsSemanticsBelow E (A, 1) w ∧
      (PointwiseEq (w ∘ donorAt₀) p) ∧ CappedEq w q γ := by
  
  let Z := (zero : State P C).normalize 1
  have hz := F.normalize_admissible (by decide : 1 ≤ 1) (F.zero_admissible 1)
  have hzc : Z.profile ∈ CanonicalPairedProfiles.inventory (Field P C) 1 :=
    normalize_inventory 1 (fun d => by cases d with
      | inl d => exact bot_ne_top
      | inr d => cases d <;> exact bot_ne_top)
  let seed : F.Anchor 1 := ⟨Z.profile, hzc, Z, hz, rfl⟩
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart seed hq hγ
  have hread' d : σ (leafSource₀ a d.1) = min (q d) γ := by
    rw [leafSource_eq]; exact hread d
  have hpr d : min (σ (SupportLadderRows.source H (fieldRank a.val (.inl d.1)))) γ =
      min (p d) γ := by
    grind only [leafSource_donor]
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ :=
    F.exists_donor_rank_repair a hσ hp hγ hpos hpr c hactive
  have hpvis (d : below₀) : SelfVis 1 (p d) := by
    have hg  :=
      le_antisymm (d.2.2.trans (min_le_left _ _)) (P.scheme.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  obtain ⟨τ, hτ, hτread, hτcap⟩ := ReceivingRankLift.exists_repaired_decoder (Y := below₀) hσ hν hcut hνread hpref hpvis hγ hpos hpr hactive
  have hcaps (d : (L).below (A, 1)) :
      min (τ (leafSource₀ b d.1)) γ = min (q d) γ := by
    rw [← hread' d]
    apply hτcap (rankIndex D hA field (F.fields 1) a d.1) (rankIndex D hA field (F.fields 1) b d.1)
      (rankIndex_bound b d.1) (rankIndex_agreement D hA field (F.fields 1) a b d.1)
    change σ (leafSource₀ a d.1) ≤ γ
    rw [hread']; exact min_le_right _ _
  refine ⟨fun d => τ (leafSource₀ b d.1),
    map_respects_of_positive_cap_agreement
      (leafSource_lawful F D sem hA field hproper hboundary b) hq
      (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps, ?_, hcaps⟩
  intro d
  exact (congrArg τ (leafSource_donor F D hA field incl hfield b d)).trans
    (hτread d)

include hboundary hfield in
/-- Every positive visible cap, including top; the inactive case is just the
lawful capped ambient, with the literal prescription pinned by its cap. -/
theorem donor_positive_lift
    {p : below₀ → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : CappedEq (q ∘ donorAt₀) p γ) :
    ∃ w , RespectsSemanticsBelow E (A, 1) w ∧
      (PointwiseEq (w ∘ donorAt₀) p) ∧ CappedEq w q γ := by
  
  by_cases hsmall : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hsmall d)),
      fun _ => by rw [min_assoc, min_self]⟩
  · obtain ⟨c, hc⟩ := not_forall.mp hsmall
    exact donor_active_lift F D sem hA field hproper hboundary incl hfield
      hp hq hγ hpos hag c (not_le.mp hc)

