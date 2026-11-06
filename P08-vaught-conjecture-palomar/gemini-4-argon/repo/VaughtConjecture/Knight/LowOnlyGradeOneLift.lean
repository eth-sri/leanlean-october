/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyGradeOneSource
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # Positive-cap private lifting on the padded LOW grade-one layer

The old-boundary interpretation and occurrence map are explicit inputs. No
physical source lawfulness, source cut, replacement anchor, alignment, output
lawfulness or predecessor lift is supplied. Actual installed ladder lawfulness
is derived from the original-boundary interpretation. This module makes no
claim about higher layers or bottom-cap supply.

The rank-table endgame follows `ReceivingGradeOneActiveLift`, specialized here
to the LOW birth-grade catalogue and the actual `RelativeLadderLayer` rows.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnly.Family
open Transform Value ExtOrd CappedDonor CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition RelativeLadderLayer

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)
  {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : ∀ d, D.scope d ≠ A)
  (hboundary : ∀ S : State P C, F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))
  (incl : C.scheme.below (effC n 1) → D.below (A, 1))
  (hfield : ∀ (S : State P C), F.Admissible 1 S → ∀ d,
    S.profile (field (incl d).1) = S.v d.1)

local notation "L" => carrier D hA (X := Field P C) (Q := F.Anchor 1)
local notation "Lbelow" => CellScheme.below (carrier D hA (X := Field P C) (Q := F.Anchor 1))
local notation "E" => rows D sem hA field (F.fields 1) hproper
local notation "H" => rungs (X := Field P C)
local notation "rkIdx" => rankIndex D hA field (F.fields 1)

def privateAt (d : C.scheme.below (effC n 1)) : Lbelow (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

def leafSource (a : F.Anchor 1) (d : Cell L) : ExtOrd :=
  image D hA field (F.fields 1) a (SupportLadderRows.source H) d

local notation "src" => leafSource F D hA field

section Face
variable (O : SemScheme n) (inclO : O.scheme.below (effC n 1) → D.below (A, 1))
  (pick : Cell O.scheme → Field P C)
  (hfieldO : ∀ (a : F.Anchor 1) d, a.val (field (inclO d).1) = a.val (pick d.1))

include hboundary hfieldO in
theorem face_positive_lift
    {p : O.scheme.below (effC n 1) → ExtOrd} {q : Lbelow (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q ⟨old D hA (inclO d).1, by rw [old_index]; exact (inclO d).2⟩) γ = min (p d) γ)
    (repair : ∀ (a : F.Anchor 1) {σ : ExtOrd → ExtOrd}, Witness (gTop 1) σ →
      (∀ d, min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ = min (p d) γ) →
      ∀ c, γ < p c →
      ∃ b : F.Anchor 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
        BoundedMap 1 ν ∧
        (∀ f, a.val f < grid 1 B ↔ σ (SupportLadderRows.source H (fieldRank a.val f)) < γ) ∧
        (∀ d, ν (b.val (pick d.1)) = p d) ∧
        ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B)) :
    ∃ w : Lbelow (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w ⟨old D hA (inclO d).1, by rw [old_index]; exact (inclO d).2⟩ = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  classical
  let _ : Fintype (O.scheme.below (effC n 1)) := Fintype.ofFinite _
  by_cases hsmall : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hsmall d)), fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hsmall
  have hactive : γ < p c := not_le.mp hc
  have hsrc_face (a : F.Anchor 1) (d : O.scheme.below (effC n 1)) :
      src a (old D hA (inclO d).1) = SupportLadderRows.source H (fieldRank a.val (pick d.1)) := by
    simp only [leafSource, image, rankIndex_old, ranks, fieldRank, fields, hfieldO a d]
  let Z := (zero : State P C).normalize 1
  let seed : F.Anchor 1 := ⟨Z.profile,
    normalize_inventory 1 fun d => by cases d with | inl _ => exact bot_ne_top | inr d => cases d <;> exact bot_ne_top,
    Z, F.normalize_admissible le_rfl (F.zero_admissible 1), rfl⟩
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart D sem hA field (F.fields 1) hproper seed hq hγ
  have hread' (d : Lbelow (A, 1)) : σ (src a d.1) = min (q d) γ := hread d
  have hpr (d) : min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ =
      min (p d) γ := by
    rw [← hsrc_face a d,
      hread' ⟨old D hA (inclO d).1, by rw [old_index]; exact (inclO d).2⟩,
      min_assoc, min_self]
    exact hag d
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ := repair a hσ hpr c hactive
  let δ := grid 1 B
  let k := next (values a.val) δ
  let f (i : ℕ) : ExtOrd := σ (SupportLadderRows.source H i)
  have hf : Monotone f := hσ.mono.comp (SupportLadderRows.source_mono H)
  have hf0 : f 0 = ⊥ := by simp only [f, SupportLadderRows.source_zero, hσ.bot]
  have hfieldc : δ ≤ a.val (pick c.1) := not_lt.mp fun hh => by
    have hl := (hcut (pick c.1)).mp hh
    have he := hpr c; rw [min_eq_left hl.le, min_eq_right hactive.le] at he
    exact hl.ne he
  have hcmem : a.val (pick c.1) ∈ values a.val :=
    mem_values.mpr ⟨ne_of_gt ((bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le hfieldc), _, rfl⟩
  have hkc : k ≤ (values a.val).card :=
    (not_lt.mp fun h => ((rank_lt_next hcmem).mp h).not_ge hfieldc).trans
      (rank_le_card _ (a.val (pick c.1)))
  have hkpos : 0 < k := Nat.succ_pos _
  have hab : FiniteProfileControllers.Agree (fieldRank a.val) (fieldRank b.val) k :=
    fieldRank_agreement (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)) hpref
  have hiff {i : ℕ} (hi : 0 < i) (hle : i ≤ (values a.val).card) : i < k ↔ f i < γ := by
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank a.val hi hle
    have hdb : a.val d ≠ ⊥ := fun he => by
      have hr : fieldRank a.val d = 0 := by simp only [fieldRank, he, rank_bot (bot_not_values _)]
      omega
    exact hd ▸ (rank_lt_next (h := δ) (mem_values.mpr ⟨hdb, d, rfl⟩) :
      fieldRank a.val d < k ↔ a.val d < δ).trans (hcut d)
  have hlow (i) (hi : i < k) : f i < γ := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos_i
    · rw [hf0]; exact hpos
    · exact (hiff hpos_i (hi.le.trans hkc)).mp hi
  have hreach : γ ≤ f k := not_lt.mp fun hl => (lt_irrefl k) ((hiff hkpos hkc).mpr hl)
  obtain ⟨g, hg, hg0, hgv, hglow, hgreach, hgread⟩ := ReceivingRankLift.exists_table
    (fun d : O.scheme.below (effC n 1) => fieldRank a.val (pick d.1))
    (fun d : O.scheme.below (effC n 1) => fieldRank b.val (pick d.1)) p f
    hkpos hf hf0
    (fun _ => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (fun d => (le_antisymm (d.2.2.trans (min_le_left _ _)) (O.scheme.grade_pos d.1) :
      O.scheme.grade d.1 = 1) ▸ (hp.orderly d).symm)
    hγ hlow hreach (fun d => hab (pick d.1)) hpr fun d e h => by
      rw [← hνread d, ← hνread e]
      exact hν.mono (not_lt.mp fun hh =>
        (rank_strict (mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩) hh).not_ge h)
  obtain ⟨τ, hτ, hτread⟩ := ReceivingRankLift.exists_rank_decoder H g hg hg0 hgv
  have hcaps (d : Lbelow (A, 1)) : min (τ (src b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H (rkIdx b d.1))) γ = _
    rw [hτread _ (rankIndex_bound D hA field (F.fields 1) b d.1), ← hread' d]
    change min (g _) γ = f _
    have hkbound : k ≤ H := hkc.trans ((values_card_le a.val).trans (Nat.le_succ _))
    have hc := FiniteProfileControllers.le_cut hkbound hab
    have hh : min (rkIdx a d.1) (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) =
        min (rkIdx b d.1) (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) :=
      rankIndex_agreement D hA field (F.fields 1) a b d.1
    by_cases hia : rkIdx a d.1 < k
    · rw [show rkIdx b d.1 = rkIdx a d.1 by omega, hglow _ hia, min_eq_left (hlow _ hia).le]
    · rw [min_eq_right (hgreach.trans (hg (by omega)))]
      exact le_antisymm (hreach.trans (hf (not_lt.mp hia)))
        (by change σ (src a d.1) ≤ γ; rw [hread']; exact min_le_right _ _)
  have hlaw : RespectsSemanticsBelow E (A, 1) (fun d => src b d.1) := by
    refine ladder_respects D sem hA field (F.fields 1) hproper (fun a' => ?_)
      (SupportLadderRows.leaf (Nat.succ_pos _) b)
    obtain ⟨S, hs, he⟩ := a'.property.2
    have hv : (fun d : D.below (A, 1) => F.fields 1 a' (field d.1)) =
        fun d => S.profile (field d.1) := funext fun d => (congrFun he _).symm
    exact hv ▸ hboundary S hs
  refine ⟨fun d => τ (src b d.1),
    map_respects_of_positive_cap_agreement hlaw hq (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps,
    fun d => (congrArg τ (hsrc_face b d)).trans
      ((hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d)),
    hcaps⟩

end Face

include hboundary hfield in
/-- Every positive visible cap, including top; the inactive case is just the
lawful capped ambient, with the literal prescription pinned by its cap. -/
theorem private_positive_lift
    {p : C.scheme.below (effC n 1) → ExtOrd} {q : Lbelow (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (privateAt F D hA incl d)) γ = min (p d) γ) :
    ∃ w : Lbelow (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt F D hA incl d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  face_positive_lift F D sem hA field hproper hboundary C incl (.inr ∘ .inl)
    (fun a d => by obtain ⟨S, hs, he⟩ := a.property.2; rw [← he]; exact hfield S hs d)
    hp hq hγ hpos hag fun a _ hσ hpr c hactive =>
      F.exists_private_rank_repair a hσ hp hγ hpos hpr c hactive

