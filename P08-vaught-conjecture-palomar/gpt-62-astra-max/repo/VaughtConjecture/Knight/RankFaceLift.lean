/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RankRepair
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # Passage from repaired field ranks to a lawful lift on the physical ladder -/

@[expose] public section
namespace VaughtConjecture.Knight.RankRepair
open Transform Value ExtOrd LadderScalarRendering CanonicalPairedInverse RelativeLadderLayer SharpWitnessComposition
noncomputable section
variable {ι X Y Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] [Finite Y] {A : Finset ι}
  {D : CellScheme A} {sem : Semantics D} {hA : 0 < A.card} {field : Cell D → X}
  {profile : Q → X → ExtOrd} {proper : ∀ d, D.scope d ≠ A}

local notation "H" => rungs (X := X)
local notation "L" => carrier D hA (X := X) (Q := Q)
local notation "E" => rows D sem hA field profile proper
local notation "src" => fun (b : Q) => image D hA field profile b (SupportLadderRows.source H)
local notation "idx" => rankIndex D hA field profile

theorem lift (seed : Q) {face : Y → (L).below (A, 1)} {pick : Y → X}
    (hface : ∀ b d, src b (face d).1 = SupportLadderRows.source H (fieldRank (profile b) (pick d)))
    (lawful : ∀ b, RespectsSemanticsBelow E (A, 1) (fun d => src b d.1))
    {q : (L).below (A, 1) → ExtOrd} (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ) {p : Y → ExtOrd}
    (hpv : ∀ d, SelfVis 1 (p d)) (hag : ∀ d, min (q (face d)) γ = min (p d) γ)
    {c} (hactive : γ < p c)
    (repair : ∀ a {σ}, Witness (gTop 1) σ → (∀ d, min (chart (profile a) σ (pick d)) γ = min (p d) γ) →
      Repaired profile (profile a) pick σ p γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧ (∀ d, w (face d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  obtain ⟨a, σ, hσ, hb, hread⟩ := exists_capped_leaf_chart D sem hA field profile proper seed hq hγ
  have read (d) : σ (src a d.1) = min (q d) γ := hread d
  have agree (d) : min (chart (profile a) σ (pick d)) γ = min (p d) γ := by
    rw [chart, ← hface, read, min_assoc, min_self]; exact hag d
  obtain ⟨b, ν, B, hν, hcut, literal, hpref⟩ := repair a hσ agree
  let δ := grid 1 B
  let k := next (values (profile a)) δ
  let f := σ ∘ SupportLadderRows.source H
  have hf : Monotone f := hσ.mono.comp (SupportLadderRows.source_mono H)
  have zero : f 0 = ⊥ := by simp [f, SupportLadderRows.source_zero, hσ.bot]
  have pos : ⊥ < δ := bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)
  have hk : 0 < k := Nat.succ_pos _
  have atRank (x) : f (fieldRank (profile a) x) < γ ↔ fieldRank (profile a) x < k := by
    by_cases h : profile a x = ⊥
    · simp only [fieldRank, h, rank_bot (bot_not_values _), zero, hpos, hk]
    · exact (hcut x).symm.trans (rank_lt_next (mem_values.mpr ⟨h, x, rfl⟩)).symm
  have atC : k ≤ fieldRank (profile a) (pick c) := le_of_not_gt fun h =>
    ((atRank _).mpr h).not_ge (min_eq_right_iff.mp ((agree c).trans (min_eq_right hactive.le)))
  have bound := atC.trans (rank_le_card _ _)
  have tracked {i} (hi : 0 < i) (hi' : i ≤ (values (profile a)).card) : f i < γ ↔ i < k := by
    obtain ⟨x, rfl⟩ := ReceivingRankLift.exists_field_rank _ hi hi'
    exact atRank x
  have low (i) (hi : i < k) : f i < γ := by
    obtain rfl | h := Nat.eq_zero_or_pos i
    · simpa only [zero] using hpos
    · exact (tracked h (hi.le.trans bound)).mpr hi
  have reach : γ ≤ f k := not_lt.mp (fun h => (lt_irrefl _) ((tracked hk bound).mp h))
  have same := fieldRank_agreement pos hpref
  have ordered (d e) (h : fieldRank (profile b) (pick d) ≤ fieldRank (profile b) (pick e)) : p d ≤ p e := by
    rw [← literal d, ← literal e]
    apply hν.mono
    by_contra! hn
    exact (rank_strict (mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hn), _, rfl⟩) hn).not_ge h
  obtain ⟨g, hg, hg0, hgv, glo, greach, gread⟩ := ReceivingRankLift.exists_table _ _ p f hk hf zero
    (fun i => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    hpv hγ low reach (fun d => same (pick d)) agree ordered
  obtain ⟨τ, hτ, dec⟩ := ReceivingRankLift.exists_rank_decoder H g hg hg0 hgv
  have caps (d : (L).below (A, 1)) : min (τ (src b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H (idx b d.1))) γ = _
    rw [dec _ (rankIndex_bound D hA field profile b d.1), ← read d]
    change min (g _) γ = f _
    have hc := FiniteProfileControllers.le_cut (bound.trans ((values_card_le _).trans (Nat.le_succ _))) same
    have he := rankIndex_agreement D hA field profile a b d.1
    let cut := FiniteProfileControllers.cut H (fieldRank (profile a)) (fieldRank (profile b))
    change k ≤ cut at hc
    change min (idx a d.1) cut = min (idx b d.1) cut at he
    by_cases hi : idx a d.1 < k
    · rw [show idx b d.1 = idx a d.1 by omega, glo _ hi, min_eq_left (low _ hi).le]
    · rw [min_eq_right (greach.trans (hg (by omega : k ≤ idx b d.1)))]
      exact le_antisymm (reach.trans (hf (not_lt.mp hi))) (hb _)
  refine ⟨_, map_respects_of_positive_cap_agreement (lawful b) hq (fun d => d.2.2) hτ hpos.ne' caps, ?_, caps⟩
  intro d
  exact (congrArg τ (hface b d)).trans ((dec _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (gread d))

end
end VaughtConjecture.Knight.RankRepair
