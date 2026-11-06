/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthBaseSupply
public import VaughtConjecture.Knight.GrowthGradeOneSource
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # All-cap original-face lifting on the growth padded base

The rank-table endgame of `LowOnlyGradeOneLift` is reused on the growth
catalogue. Both public endpoints construct their source repair from the
arbitrary physical query; the donor endpoint uses the pre-activation fibre.
Caps are proved at every occurrence before positive-cap transport is applied.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth CanonicalPairedInverse LadderScalarRendering SharpWitnessComposition RelativeLadderLayer

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "L" => scheme I X hA
local notation "Lbelow" => CellScheme.below (scheme I X hA)
local notation "E" => semantics I X hA hB hC
local notation "H" => rungs (X := Field I.right.scheme I.left.scheme)
local notation "rkIdx" => rankIndex I.boundary hA (field I) (fields I X)

def source (a : Catalogue X 1) (d : Cell L) : ExtOrd :=
  image I.boundary hA (field I) (fields I X) a (SupportLadderRows.source H) d

local notation "src" => source I X hA

section Face
variable {s : ℕ} (O : SemScheme s)
  (incl : O.scheme.below (Finset.univ, 1) → I.boundary.below (A, 1))
  (pick : Cell O.scheme → Field I.right.scheme I.left.scheme)
  (hfield : ∀ a : Catalogue X 1, ∀ d, a.val (field I (incl d).1) = a.val (pick d.1))

include T hfield in
private theorem face_lift
    {p : O.scheme.below (Finset.univ, 1) → ExtOrd} {q : Lbelow (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow O.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (oldAt I X hA (incl d))) γ = min (p d) γ)
    (bot_supply : ∃ w, RespectsSemanticsBelow E (A, 1) w ∧ ∀ d, w (oldAt I X hA (incl d)) = p d)
    (repair : ∀ (a : Catalogue X 1) {σ : ExtOrd → ExtOrd}, Witness (gTop 1) σ →
      ⊥ < γ →
      (∀ d, min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ = min (p d) γ) →
      ∀ c, γ < p c →
      ∃ b : Catalogue X 1, ∃ ν : ExtOrd → ExtOrd, ∃ B : ℕ,
        BoundedMap 1 ν ∧
        (∀ f, a.val f < grid 1 B ↔ σ (SupportLadderRows.source H (fieldRank a.val f)) < γ) ∧
        (∀ d, ν (b.val (pick d.1)) = p d) ∧
        ∀ f, min (a.val f) (grid 1 B) = min (b.val f) (grid 1 B)) :
    ∃ w : Lbelow (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (oldAt I X hA (incl d)) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ := by
  classical
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := bot_supply
    exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
  by_cases hi : ∀ d, p d ≤ γ
  · exact ⟨fun d => min (q d) γ, hq.cap hγ,
      fun d => (hag d).trans (min_eq_left (hi d)), fun _ => by rw [min_assoc, min_self]⟩
  obtain ⟨c, hc⟩ := not_forall.mp hi
  have hpos : ⊥ < γ := bot_lt_iff_ne_bot.mpr hz
  have hactive : γ < p c := not_le.mp hc
  have hsrc_face (a : Catalogue X 1) (d : O.scheme.below (Finset.univ, 1)) :
      src a (oldAt I X hA (incl d)).1 = SupportLadderRows.source H (fieldRank a.val (pick d.1)) := by
    simp only [source, oldAt, image, rankIndex_old, ranks, fieldRank, fields, hfield a d]
  let Z := (zero : State I.right.scheme I.left.scheme).normalize 1
  let seed : Catalogue X 1 := ⟨Z.profile,
    normalize_inventory 1 fun d => by cases d <;> exact bot_ne_top,
    Z, normalize_admitted X le_rfl (zero_admitted X 1), rfl⟩
  obtain ⟨a, σ, hσ, _, hread⟩ :=
    exists_capped_leaf_chart I.boundary I.rows hA (field I) (fields I X) (proper I hB hC) seed hq hγ
  have hread' (d : Lbelow (A, 1)) : σ (src a d.1) = min (q d) γ := hread d
  have hpr (d) : min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ =
      min (p d) γ := by
    rw [← hsrc_face a d, hread', min_assoc, min_self]; exact hag d
  obtain ⟨b, ν, B, hν, hcut, hνread, hpref⟩ := repair a hσ hpos hpr c hactive
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
    (fun d : O.scheme.below (Finset.univ, 1) => fieldRank a.val (pick d.1))
    (fun d : O.scheme.below (Finset.univ, 1) => fieldRank b.val (pick d.1)) p f
    hkpos hf hf0
    (fun _ => CappedDonor.Ref.selfVis_map hσ le_rfl (SupportLadderRows.source_visible _ _))
    (fun d => (le_antisymm d.2.2 (O.scheme.grade_pos d.1) : O.scheme.grade d.1 = 1) ▸
      (hp.orderly d).symm)
    hγ hlow hreach (fun d => hab (pick d.1)) hpr fun d e h => by
      rw [← hνread d, ← hνread e]
      exact hν.mono (not_lt.mp fun hh =>
        (rank_strict (mem_values.mpr ⟨ne_of_gt (bot_le.trans_lt hh), _, rfl⟩) hh).not_ge h)
  obtain ⟨τ, hτ, hτread⟩ := ReceivingRankLift.exists_rank_decoder H g hg hg0 hgv
  have hcaps (d : Lbelow (A, 1)) : min (τ (src b d.1)) γ = min (q d) γ := by
    change min (τ (SupportLadderRows.source H (rkIdx b d.1))) γ = _
    rw [hτread _ (rankIndex_bound I.boundary hA (field I) (fields I X) b d.1), ← hread' d]
    change min (g _) γ = f _
    have hkbound : k ≤ H := hkc.trans ((values_card_le a.val).trans (Nat.le_succ _))
    have hc := FiniteProfileControllers.le_cut hkbound hab
    have hh : min (rkIdx a d.1) (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) =
        min (rkIdx b d.1) (FiniteProfileControllers.cut H (fieldRank a.val) (fieldRank b.val)) :=
      rankIndex_agreement I.boundary hA (field I) (fields I X) a b d.1
    by_cases hia : rkIdx a d.1 < k
    · rw [show rkIdx b d.1 = rkIdx a d.1 by omega, hglow _ hia, min_eq_left (hlow _ hia).le]
    · rw [min_eq_right (hgreach.trans (hg (by omega)))]
      exact le_antisymm (hreach.trans (hf (not_lt.mp hia)))
        (by change σ (src a d.1) ≤ γ; rw [hread']; exact min_le_right _ _)
  refine ⟨fun d => τ (src b d.1),
    map_respects_of_positive_cap_agreement
      (ladder_respects I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)
        (anchor_lawful I X T) (SupportLadderRows.leaf (Nat.succ_pos _) b))
      hq (fun d => d.2.2) hτ (ne_of_gt hpos) hcaps,
    fun d => (congrArg τ (hsrc_face b d)).trans
      ((hτread _ (Nat.le_succ_of_le (fieldRank_le _ _))).trans (hgread d)),
    hcaps⟩

end Face

include T in
theorem private_lift
    {p : I.right.scheme.below (Finset.univ, 1) → ExtOrd}
    {q : Lbelow (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (privateAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt I X hA d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  face_lift I X T hA hB hC I.right (privateIncl I) Sum.inl
    (fun a d => by obtain ⟨S, hs, he⟩ := a.property.2; rw [← he]; exact field_private I X T hs d.1)
    hp hq hγ hag (private_bottom_supply I X T hA hB hC hp)
    fun a _ hσ hpos hpr c hactive => exists_private_rank_repair X T a hσ hp hγ hpos hpr c hactive

include T in
theorem donor_lift (hN : 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 1) → ExtOrd}
    {q : Lbelow (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (donorAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  face_lift I X T hA hB hC I.left (donorIncl I) Sum.inr
    (fun a d => by obtain ⟨S, _, he⟩ := a.property.2; rw [← he]; exact field_donor I S d.1)
    hp hq hγ hag (donor_bottom_supply I X T hA hB hC hN hp)
    fun a _ hσ hpos hpr c hactive => exists_donor_rank_repair X T hN a hσ hp hγ hpos hpr c hactive

include T in
/-- The intended strict donor-arity geometry discharges pre-activation. -/
theorem donor_lift_of_arity (hsmall : n + 1 < X.req.N)
    {p : I.left.scheme.below (Finset.univ, 1) → ExtOrd}
    {q : Lbelow (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (donorAt I X hA d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  donor_lift I X T hA hB hC ((Nat.succ_le_succ (Nat.zero_le n)).trans_lt hsmall) hp hq hγ hag

