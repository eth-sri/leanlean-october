/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RankRepair
public import VaughtConjecture.Knight.RelativeLadderAmbient
public import VaughtConjecture.Knight.PaddedFaceLift
public import VaughtConjecture.Knight.RelativeLadderRankRendering

@[expose] public section

namespace VaughtConjecture.Knight.RelativeLadderLayer

open Transform Value ExtOrd CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd) (proper : ∀ d, D.scope d ≠ A)

local notation "L" => carrier D hA (X := X) (Q := Q)

local notation "E" => rows D sem hA field fields proper

local notation "H" => rungs (X := X)

def rankSource (a : Q) (d : Cell L) : ExtOrd := image D hA field fields a (SupportLadderRows.source H) d

def prescribedAt (d : D.below (A, 1)) : (L).below (A, 1) :=
  ⟨old D hA d.1, by rw [old_index]; exact d.2⟩

variable {κ : Type*} [DecidableEq κ] {B : Finset κ} {O : CellScheme B} {os : Semantics O}
  {BJ : Finset κ × ℕ} (hj : BJ.2 ≤ 1)
  (incl : O.below BJ → D.below (A, 1)) (pick : O.below BJ → X)
  (hfield : ∀ a d, fields a (field (incl d).1) = fields a (pick d))

include hfield in
private theorem rankSource_at (a : Q) (d : O.below BJ) :
    rankSource D hA field fields a (prescribedAt D hA (incl d)).1 =
      SupportLadderRows.source H (fieldRank (fields a) (pick d)) := by simp [rankSource, prescribedAt, image, rankIndex_old, ranks, fieldRank, hfield a d]

variable (birth : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1)))
  (seed : Q) (repair : RankRepair.IsRepair fields (RespectsSemanticsBelow os BJ) pick)
  {p : O.below BJ → ExtOrd} {q : (carrier D hA (X := X) (Q := Q)).below (A, 1) → ExtOrd}
  (hp : RespectsSemanticsBelow os BJ p) (hq : RespectsSemanticsBelow (rows D sem hA field fields proper) (A, 1) q)
  {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
  (hag : ∀ d, min (q (prescribedAt D hA (incl d))) γ = min (p d) γ)

include hj birth seed hfield repair hp hq hγ hpos hag in
private theorem rank_active_lift (c : O.below BJ) (hactive : γ < p c) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (prescribedAt D hA (incl d)) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  classical
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart D sem hA field fields proper seed hq hγ
  have hread' (d) : σ (rankSource D hA field fields a d.1) = min (q d) γ := by
    exact hread d
  have hpr (d) : min (σ (SupportLadderRows.source H (fieldRank (fields a) (pick d)))) γ =
      min (p d) γ := by
    rw [← rankSource_at D hA field fields incl pick hfield a d,
      hread', min_assoc, min_self]
    exact hag d
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ :=
    repair a hσ hp hγ hpos hpr c hactive
  let δ := grid 1 B
  let k := next (values (fields a)) δ
  let f : ℕ → ExtOrd := fun i => σ (SupportLadderRows.source H i)
  have hf : Monotone f := hσ.mono.comp (SupportLadderRows.source_mono H)
  have hf0 : f 0 = ⊥ := by simp only [f, SupportLadderRows.source_zero, hσ.bot]
  have hfv (i) : SelfVis 1 (f i) :=
    CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _)
  have hfieldc : δ ≤ (fields a) (pick c) := by
    grind
  have hcmem : (fields a) (pick c) ∈ values (fields a) :=
    mem_values.mpr ⟨ne_of_gt ((bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le hfieldc), _, rfl⟩
  have hkc : k ≤ (values (fields a)).card := by
    apply le_trans _ (rank_le_card _ ((fields a) (pick c)))
    apply not_lt.mp
    intro h
    exact ((rank_lt_next hcmem).mp h).not_ge hfieldc
  have hkpos : 0 < k := Nat.succ_pos _
  have hkbound : k ≤ H := hkc.trans ((values_card_le (fields a)).trans (Nat.le_succ _))
  have hab : FiniteProfileControllers.Agree (fieldRank (fields a)) (fieldRank (fields b)) k :=
    fieldRank_agreement (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)) hpref
  have hlow (i) (hi : i < k) : f i < γ := by
    by_cases hz : i = 0
    · lia
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank (fields a)
      (Nat.pos_of_ne_zero hz) (hi.le.trans hkc)
    have hdb : (fields a) d ≠ ⊥ := by
      intro he
      have hr : fieldRank (fields a) d = 0 := by simp [fieldRank, he, rank_bot (bot_not_values _)]
      omega
    have hr : fieldRank (fields a) d < next (values (fields a)) δ := hd ▸ hi
    have hl := (rank_lt_next (mem_values.mpr ⟨hdb, d, rfl⟩)).mp hr
    grind
  have hreach : γ ≤ f k := by
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank (fields a) hkpos hkc
    apply not_lt.mp
    intro hl
    have hlt : (fields a) d < δ := by grind
    have hdb : (fields a) d ≠ ⊥ := by
      intro he
      have hr : fieldRank (fields a) d = 0 := by simp [fieldRank, he, rank_bot (bot_not_values _)]
      have := hd.symm.trans hr
      omega
    have hr := (rank_lt_next (mem_values.mpr ⟨hdb, d, rfl⟩)).mpr hlt
    change fieldRank (fields a) d < k at hr
    omega
  have hpvis (d : O.below BJ) : SelfVis 1 (p d) := by
    have hg : O.grade d.1 = 1 :=
      le_antisymm (d.2.2.trans hj) (O.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  have horder (d e : O.below BJ)
      (h : fieldRank (fields b) (pick d) ≤ fieldRank (fields b) (pick e)) : p d ≤ p e := by
    rw [← hνread d, ← hνread e]
    apply hν.mono
    by_contra hn
    have hh := not_le.mp hn
    have hm : (fields b) (pick d) ∈ values (fields b) :=
      mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩
    exact (rank_strict hm hh).not_ge h
  obtain ⟨g, hg, hg0, hgv, hglow, hgreach, hgread⟩ := ReceivingRankLift.exists_table
    (fun d : O.below BJ => fieldRank (fields a) (pick d))
    (fun d : O.below BJ => fieldRank (fields b) (pick d)) p f
    hkpos hf hf0 hfv hpvis hγ hlow hreach (fun d => hab (pick d)) hpr horder
  obtain ⟨τ, hτ, hτread⟩ := ReceivingRankLift.exists_rank_decoder H g hg hg0 hgv
  have hcaps (d : (L).below (A, 1)) :
      min (τ (rankSource D hA field fields b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H
      (rankIndex D hA field fields b d.1))) γ = _
    rw [hτread _ (rankIndex_bound D hA field fields b d.1), ← hread' d]
    change min (g _) γ = f _
    have hc := FiniteProfileControllers.le_cut hkbound hab
    have hh := rankIndex_agreement D hA field fields a b d.1
    change min (rankIndex D hA field fields a d.1)
      (FiniteProfileControllers.cut H (fieldRank (fields a)) (fieldRank (fields b))) =
      min (rankIndex D hA field fields b d.1)
      (FiniteProfileControllers.cut H (fieldRank (fields a)) (fieldRank (fields b))) at hh
    by_cases hia : rankIndex D hA field fields a d.1 < k
    · grind
    · have hib : k ≤ rankIndex D hA field fields b d.1 := by omega
      rw [min_eq_right (hgreach.trans (hg hib))]
      have hle : γ ≤ f (rankIndex D hA field fields a d.1) :=
        hreach.trans (hf (not_lt.mp hia))
      grind
  refine ⟨fun d => τ (rankSource D hA field fields b d.1),
    map_respects_of_positive_cap_agreement
      (ladder_respects D sem hA field fields proper birth (SupportLadderRows.leaf (Nat.succ_pos _) b)) hq
      (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps, ?_, hcaps⟩
  intro d
  exact (congrArg τ (rankSource_at D hA field fields incl pick hfield b d)).trans
    ((hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d))

include hj birth seed hfield repair hp hq hγ hpos hag in
/-- Positive-cap lifts use the shared rank table; the bounded prescription needs only capping. -/
theorem rank_positive_lift :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (prescribedAt D hA (incl d)) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  by_cases hi : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      by simp_all, by simp⟩
  obtain ⟨c, hc⟩ := not_forall.mp hi
  exact rank_active_lift D sem hA field fields proper hj incl pick hfield birth seed repair
    hp hq hγ hpos hag c (not_le.mp hc)

section Fibre

variable {S : Type*} (C : TerminalProfile.Context S X) [Fintype (C.Anchor 1)]

local notation "fields₁" => (Subtype.val : C.Anchor 1 → X → ExtOrd)

include hj in
/-- The grade-one rank ladder uses the same scalar fibre as the higher layers. -/
theorem lift_fibre (F : C.Fibre 1 (fun d => field (incl d).1) (RespectsSemanticsBelow os BJ))
    (vis : ∀ s, C.admitted 1 s → ∀ f, SelfVis 1 (C.profile s f))
    (law : ∀ s, C.admitted 1 s → RespectsSemanticsBelow sem (A, 1) (fun d => C.profile s (field d.1)))
    (seed : C.Anchor 1) :
    PaddedFaceLift.Lift os (rows D sem hA field fields₁ proper) (prescribedAt D hA ∘ incl) := by
  intro p q hp hq γ hγ hag
  by_cases hbot : γ = ⊥
  · obtain ⟨s, hs, hr⟩ := F.bottom hp
    obtain ⟨a, ha⟩ := C.rank_anchor le_rfl hs
    exact ⟨fun d => renderWith D hA field fields₁ a (C.profile s) ⊤ d.1,
      renderWith_respects D sem hA field fields₁ proper a (C.profile s) ha (fun _ => le_top)
        (vis s hs) (extVisibilityReplace_top 1 1) (law s hs),
      fun d => (renderWith_old D hA field fields₁ a (C.profile s) ⊤ ha (incl d).1).trans (hr d),
      fun _ => by simp only [hbot, min_bot_right]⟩
  have birth (a : C.Anchor 1) : RespectsSemanticsBelow sem (A, 1) (fun d => a.val (field d.1)) := by
    obtain ⟨s, hs, he⟩ := a.property.2
    exact he ▸ law s hs
  refine rank_positive_lift D sem hA field fields₁ proper hj incl (fun d => field (incl d).1)
    (fun _ _ => rfl) birth seed (RankRepair.of_catalogue C _ hj vis (fun _ hs => F.lawful hs) ?_)
    hp hq hγ (bot_lt_iff_ne_bot.mpr hbot) hag
  intro s B hs hc v hv hag
  obtain ⟨t, -, he, hr⟩ := F.repair hs hc hv hag
  exact ⟨t, he, hr⟩

end Fibre

end

end VaughtConjecture.Knight.RelativeLadderLayer
