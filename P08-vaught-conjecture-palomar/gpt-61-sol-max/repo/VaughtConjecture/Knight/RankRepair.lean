
import VaughtConjecture.Knight.PointwiseLabels
import VaughtConjecture.Knight.ReceivingRankLift
import VaughtConjecture.Knight.RelativeLadderLayer
import Mathlib.Tactic
namespace VaughtConjecture.Knight.ReceivingRankLift
open   ExtOrd CappedDonor CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition

variable {X Y : Type*} [Fintype X] [Finite Y]
local notation "H" => RelativeLadderLayer.rungs (X := X)

/-- The rank-table endgame depends only on the preserved prefix, not on
which private or donor face supplied the repaired field values. -/
theorem exists_repaired_decoder {a b : X → ExtOrd} {pick : Y → X}
    {p : Y → ExtOrd} {σ ν : LabelMap} {γ : ExtOrd} {B : ℕ}
    (hσ : Witness (gTop 1) σ) (hν : BoundedMap 1 ν)
    (hcut : ∀ x, a x < grid 1 B ↔
      σ (SupportLadderRows.source H (fieldRank a x)) < γ)
    (hνread : ∀ d, ν (b (pick d)) = p d)
    (hpref : CappedEq a b (grid 1 B))
    (hpvis : ∀ d, SelfVis 1 (p d)) (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hpr : ∀ d, min (σ (SupportLadderRows.source H (fieldRank a (pick d)))) γ = min (p d) γ)
    {c : Y} (hactive : γ < p c) :
    ∃ τ, BoundedMap 1 τ ∧
      (∀ d, τ (SupportLadderRows.source H (fieldRank b (pick d))) = p d) ∧
      ∀ i j, j ≤ H →
        min i (FiniteProfileControllers.cut H (fieldRank a) (fieldRank b)) =
          min j (FiniteProfileControllers.cut H (fieldRank a) (fieldRank b)) →
        σ (SupportLadderRows.source H i) ≤ γ →
        min (τ (SupportLadderRows.source H j)) γ = σ (SupportLadderRows.source H i) := by
  
  let δ := grid 1 B
  let k := next (values a) δ
  let f : ℕ → ExtOrd := fun i => σ (SupportLadderRows.source H i)
  have hf  := hσ.mono.comp (SupportLadderRows.source_mono H)
  have hf0 : f 0 = ⊥ := by simp only [f, SupportLadderRows.source_zero, hσ.bot]
  have hfv i : SelfVis 1 (f i) :=
    CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _)
  have hfieldc : δ ≤ a (pick c) := by
    grind
  have hcmem : a (pick c) ∈ values a :=
    mem_values.mpr ⟨ne_of_gt ((bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)).trans_le hfieldc), _, rfl⟩
  have hkc : k ≤ (values a).card := by
    apply le_trans _ (rank_le_card _ (a (pick c)))
    apply not_lt.mp
    intro h
    exact ((rank_lt_next hcmem).mp h).not_ge hfieldc
  have hkpos : 0 < k := Nat.succ_pos _
  have hkbound : k ≤ H := hkc.trans ((values_card_le a).trans (Nat.le_succ _))
  have hab  :=
    fieldRank_agreement (bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _)) hpref
  have hlow i (hi : i < k) : f i < γ := by
    by_cases hz : i = 0
    · rw [hz, hf0]; exact hpos
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank a
      (Nat.pos_of_ne_zero hz) (hi.le.trans hkc)
    have hdb : a d ≠ ⊥ := by
      intro he
      have hr : fieldRank a d = 0 := by simp only [fieldRank, he, rank_bot (bot_not_values)]
      exact hz (hd.symm.trans hr)
    have hr  := hd ▸ hi
    have hl := (rank_lt_next (mem_values.mpr ⟨hdb, d, rfl⟩)).mp hr
    simpa only [hd] using (hcut d).mp hl
  have hreach : γ ≤ f k := by
    obtain ⟨d, hd⟩ := ReceivingRankLift.exists_field_rank a hkpos hkc
    apply not_lt.mp
    intro hl
    have hlt  := (hcut d).mpr (by simpa only [hd] using hl)
    have hdb : a d ≠ ⊥ := by
      intro he
      have hr : fieldRank a d = 0 := by simp only [fieldRank, he, rank_bot (bot_not_values)]
      have := hd.symm.trans hr
      omega
    have hr := (rank_lt_next (mem_values.mpr ⟨hdb, d, rfl⟩)).mpr hlt
    change fieldRank a d < k at hr
    rw [show fieldRank a d = k from hd] at hr
    exact (lt_irrefl k) hr
  have horder (d e : Y) (h : fieldRank b (pick d) ≤ fieldRank b (pick e)) : p d ≤ p e := by
    rw [← hνread d, ← hνread e]
    apply hν.mono
    by_contra hn
    have hh := not_le.mp hn
    have hm : b (pick d) ∈ values b :=
      mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩
    exact (rank_strict hm hh).not_ge h
  obtain ⟨g, hg, hg0, hgv, hglow, hgreach, hgread⟩ := exists_table
    (fun d => fieldRank a (pick d)) (fun d => fieldRank b (pick d)) p f
    hkpos hf hf0 hfv hpvis hγ hlow hreach (fun d => hab (pick d)) hpr horder
  obtain ⟨τ, hτ, hτread⟩ := exists_rank_decoder H g hg hg0 hgv
  refine ⟨τ, hτ, fun d => (hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d), ?_⟩
  intro i j hj hh hbound
  rw [hτread _ hj]
  change min (g j) γ = f i
  have hc := FiniteProfileControllers.le_cut hkbound hab
  by_cases hi : i < k
  · have he : j = i := by omega
    rw [he, hglow _ hi, min_eq_left (hlow _ hi).le]
  · have hjk : k ≤ j := by omega
    rw [min_eq_right (hgreach.trans (hg hjk))]
    exact le_antisymm (hreach.trans (hf (not_lt.mp hi))) hbound

