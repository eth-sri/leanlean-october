/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.RankFaceLift
public import VaughtConjecture.Knight.GrowthBaseSupply
public import VaughtConjecture.Knight.GrowthGradeOneSource
public import VaughtConjecture.Knight.RelativeLadderAmbient

/-! # All-cap original-face lifting on the growth padded base

The rank-table endgame of `LowOnlyGradeOneLift` is reused on the growth
catalogue. Both public endpoints construct their source repair from the
arbitrary physical query; the donor endpoint uses the pre-activation fibre.
Caps are proved at every occurrence before positive-cap transport is applied.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthOrderedBase
open Transform Value ExtOrd AmalgamationPlan Growth CanonicalPairedInverse
open LadderScalarRendering SharpWitnessComposition RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.Attachment X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "L" => scheme I X hA
local notation "E" => semantics I X hA hB hC
local notation "H" => rungs (X := Field I.right.scheme I.left.scheme)

def source (a : Catalogue X 1) (d : Cell L) : ExtOrd :=
  image I.boundary hA (field I) (fields I X) a (SupportLadderRows.source H) d

theorem source_eq a d :
    source I X hA a d = ladderRow I.boundary hA (field I) (fields I X)
      (SupportLadderRows.leaf (Nat.succ_pos _) a) d := rfl

include T in
theorem source_lawful a :
    RespectsSemanticsBelow E (A, 1) (fun d => source I X hA a d.1) := by
  simp only [source_eq]
  exact ladder_respects I.boundary I.rows hA (field I) (fields I X) (proper I hB hC)
    (anchor_lawful I X T) _

section Face
variable {s : ℕ} (O : SemScheme s)
  (incl : O.Native 1 → I.boundary.below (A, 1))
  (pick : Cell O.scheme → Field I.right.scheme I.left.scheme)
  (hfield : ∀ a : Catalogue X 1, ∀ d, a.val (field I (incl d).1) = a.val (pick d.1))

include hfield in
theorem source_face a d :
    source I X hA a (oldAt I X hA (incl d)).1 =
      SupportLadderRows.source H (fieldRank a.val (pick d.1)) := by
  simp only [source, oldAt, image, rankIndex_old, ranks, fieldRank, fields, hfield a d]

include T hfield in
private theorem face_active_lift
    (repair : ∀ (a : Catalogue X 1) {σ}, Witness (gTop 1) σ →
      ∀ {p : O.scheme.below (Finset.univ, 1) → ExtOrd},
      RespectsSemanticsBelow O.rows (Finset.univ, 1) p →
      ∀ {γ}, SelfVis 1 γ → ⊥ < γ →
      (∀ d, min (σ (SupportLadderRows.source H (fieldRank a.val (pick d.1)))) γ = min (p d) γ) →
      ∀ c, γ < p c → RankRepair.Repaired (fun b : Catalogue X 1 => b.val) a.val
        (fun d => pick d.1) σ p γ)
    {p} {q}
    (hp : O.rows.Lawful p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : CappedEq (q ∘ oldAt I X hA ∘ incl) p γ)
    c (hactive : γ < p c) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (oldAt I X hA (incl d)) = p d) ∧ CappedEq w q γ := by
  classical
  let Z := (zero : State I.right.scheme I.left.scheme).normalize 1
  have hz := normalize_admitted X (by decide : 1 ≤ 1) (zero_admitted X 1)
  have hzc : Z.profile ∈ CanonicalPairedProfiles.inventory
      (Field I.right.scheme I.left.scheme) 1 :=
    normalize_inventory 1 (fun d => by cases d <;> exact bot_ne_top)
  let seed : Catalogue X 1 := ⟨Z.profile, hzc, Z, hz, rfl⟩
  have hpvis (d : O.Native 1) : SelfVis 1 (p d) := by
    have hg : O.scheme.grade d.1 = 1 :=
      le_antisymm d.2.2 (O.scheme.grade_pos d.1)
    exact hg ▸ (hp.orderly d).symm
  exact RankRepair.lift (D := I.boundary) (sem := I.rows) (hA := hA) (field := field I) (profile := fields I X)
    (proper := proper I hB hC) (face := fun d => oldAt I X hA (incl d)) seed (pick := (fun d => pick d.1)) (source_face I X hA O incl pick hfield)
    (source_lawful I X T hA hB hC) hq hγ hpos hpvis hag hactive
    (fun a _ hσ hh => repair a hσ hp hγ hpos hh c hactive)

end Face

include T in
theorem private_lift
    {p}
    {q}
    (hp : I.right.rows.Lawful p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : CappedEq (q ∘ privateAt I X hA) p γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt I X hA d) = p d) ∧
      CappedEq w q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := private_bottom_supply I X T hA hB hC hp
    exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
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
  exact field_private I X T hs d.1

include T in
theorem donor_lift (hN : 1 < X.req.N)
    {p}
    {q}
    (hp : I.left.rows.Lawful p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : CappedEq (q ∘ donorAt I X hA) p γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧
      CappedEq w q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := donor_bottom_supply I X T hA hB hC hN hp
    exact ⟨w, hw, hr, fun _ => by simp only [hz, min_bot_right]⟩
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
  exact field_donor I S d.1

include T in
/-- The intended strict donor-arity geometry discharges pre-activation. -/
theorem donor_lift_of_arity (hsmall : n + 1 < X.req.N)
    {p}
    {q}
    (hp : I.left.rows.Lawful p)
    (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : CappedEq (q ∘ donorAt I X hA) p γ) :
    ∃ w, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt I X hA d) = p d) ∧
      CappedEq w q γ :=
  donor_lift I X T hA hB hC ((Nat.succ_le_succ (Nat.zero_le n)).trans_lt hsmall)
    hp hq hγ hag

end
end VaughtConjecture.Knight.GrowthOrderedBase
