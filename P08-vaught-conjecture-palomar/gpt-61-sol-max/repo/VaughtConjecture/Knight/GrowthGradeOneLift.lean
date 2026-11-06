
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.RankRepair

import VaughtConjecture.Knight.GrowthBaseSupply
import VaughtConjecture.Knight.GrowthGradeOneSource
import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # All-cap original-face lifting on the growth padded base

The rank-table endgame of `LowOnlyGradeOneLift` is reused on the growth
catalogue. Both public endpoints construct their source repair from the
arbitrary physical query; the donor endpoint uses the pre-activation fibre.
Caps are proved at every occurrence before positive-cap transport is applied.
-/

namespace VaughtConjecture.Knight.GrowthOrderedBase
open     Growth CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "L" => scheme I X hA
local notation "E" => semantics I X hA hB hC
local notation "H" => rungs (X := Field I.right.scheme I.left.scheme)

def source a d :=
  image I.boundary hA (field I) (fields I X) a (SupportLadderRows.source H) d

local notation "source₀" => source I X hA

theorem source_eq a d :
    source₀ a d = ladderRow I.boundary hA (field I) (fields I X)
      (SupportLadderRows.leaf (Nat.succ_pos _) a) d := rfl

include T in
theorem source_lawful a :
    RespectsSemanticsBelow E (A, 1) (fun d => source₀ a d.1) := by
  simp  [source_eq]
  exact ladder_respects hA (proper hB hC)
    (anchor_lawful I X T) _

section
variable {s : ℕ} (O : SemScheme s)
  (incl : O.scheme.below (Finset.univ, 1) → I.boundary.below (A, 1))
  (pick : Cell O.scheme → Field I.right.scheme I.left.scheme)
  (hfield : ∀ a : Catalogue X 1, ∀ d, a.val (field I (incl d).1) = a.val (pick d.1))

include hfield in
theorem source_face a d :
    source₀ a (oldAt I X hA (incl d)).1 =
      SupportLadderRows.source H (fieldRank a.val (pick d.1)) := by simp_all [source, oldAt, image, ranks, fieldRank]

include T hfield in
private theorem face_active_lift
    (repair : ∀ (a : Catalogue X 1) {σ}, Witness (gTop 1) σ →
      ∀ {p},
      RespectsSemanticsBelow O.rows (Finset.univ, 1) p →
      ∀ {γ : ExtOrd}, SelfVis 1 γ → ⊥ < γ →
      (∀ d, min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ = min (p d) γ) →
      ∀ c, γ < p c →
      ∃ b : Catalogue X 1, ∃ ν : LabelMap, ∃ B : ℕ,
        BoundedMap 1 ν ∧
        (∀ f, a.val f < grid 1 B ↔ σ (SupportLadderRows.source H (fieldRank a.val f)) < γ) ∧
        (∀ d, ν (b.val (pick d.1)) = p d) ∧
        CappedEq a.val b.val (grid 1 B))
    {p} {q}
    (hp : RespectsSemanticsBelow O.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (oldAt I X hA (incl d))) γ = min (p d) γ)
    c (hactive : γ < p c) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (oldAt I X hA (incl d)) = p d) ∧ CappedEq w q γ := by
  classical
  let Z := (zero : State I.right.scheme I.left.scheme).normalize 1
  have hz := normalize_admitted X (j := 1) (by decide) (zero_admitted X)
  have hzc : Z.profile ∈ CanonicalPairedProfiles.inventory
      (Field I.right.scheme I.left.scheme) 1 :=
    normalize_inventory 1 (fun d => by cases d <;> exact bot_ne_top)
  let seed : Catalogue X 1 := ⟨Z.profile, hzc, Z, hz, rfl⟩
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart seed hq hγ
  have hread' (d) : σ (source₀ a d.1) = min (q d) γ := by
    rw []; exact hread d
  have hpr (d) : min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ =
      min (p d) γ := by
    rw [← source_face I X hA O incl pick hfield a d,
      hread', min_assoc, min_self]
    exact hag d
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ :=
    repair a hσ hp hγ hpos hpr c hactive
  have hpvis (d : O.scheme.below (Finset.univ, 1)) : SelfVis 1 (p d) := by
    have hg : O.scheme.grade d.1 = 1 :=
      le_antisymm d.2.2 (O.scheme.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  obtain ⟨τ, hτ, hτread, hτcap⟩ := ReceivingRankLift.exists_repaired_decoder  hσ hν hcut hνread hpref hpvis hγ hpos hpr hactive
  have hcaps (d : (L).below (A, 1)) :
      min (τ (source₀ b d.1)) γ = min (q d) γ := by
    rw [← hread' d]
    apply hτcap (rankIndex I.boundary hA (field I) (fields I X) a d.1) (rankIndex I.boundary hA (field I) (fields I X) b d.1)
      (rankIndex_bound b d.1) (rankIndex_agreement I.boundary hA (field I) (fields I X) a b d.1)
    change σ (source₀ a d.1) ≤ γ
    rw [hread']; exact min_le_right _ _
  refine ⟨fun d => τ (source₀ b d.1),
    map_respects_of_positive_cap_agreement
      (source_lawful I X T hA hB hC b) hq
      (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps, ?_, hcaps⟩
  intro d
  exact (congrArg τ (source_face I X hA O incl pick hfield b d)).trans
    (hτread d)

end

include T in
theorem private_lift
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (privateAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt I X hA d) = p d) ∧
      CappedEq w q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := private_bottom_supply I X T hA hB hC hp
    exact ⟨w, hw, hr, fun _ => by simp  [hz, ]⟩
  by_cases hi : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hi d)),
      fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hi
  apply face_active_lift I X T hA hB hC I.right (privateIncl I) Sum.inl
    (fun a d => ?_) (exists_private_rank_repair X T) hp hq hγ
    (bot_lt_iff_ne_bot.mpr hz) hag c (not_le.mp hc)
  obtain ⟨S, hs, he⟩ := a.property.2
  rw [← he]
  exact field_private T hs d.1

include T in
theorem donor_lift (hN : 1 < X.req.N)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (donorAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧
      CappedEq w q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := donor_bottom_supply I X T hA hB hC hN hp
    exact ⟨w, hw, hr, fun _ => by simp  [hz, ]⟩
  by_cases hi : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hi d)),
      fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hi
  apply face_active_lift I X T hA hB hC I.left (donorIncl I) Sum.inr
    (fun a d => ?_) (exists_donor_rank_repair X T hN) hp hq hγ
    (bot_lt_iff_ne_bot.mpr hz) hag c (not_le.mp hc)
  obtain ⟨S, _, he⟩ := a.property.2
  rw [← he]
  exact field_donor I

include T in
/-- The intended strict donor-arity geometry discharges pre-activation. -/
def donor_lift_of_arity (hsmall : n + 1 < X.req.N)
    {p}
    {q}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (donorAt I X hA d)) γ = min (p d) γ) :=
  donor_lift I X T hA hB hC ((Nat.succ_le_succ (Nat.zero_le n)).trans_lt hsmall)
    hp hq hγ hag

