
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyOrderedLadder
import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # Independent physical bottom supply on the unchanged LOW ladder

Terminal properization and normalization select an installed anchor with the
same complete field ranks. Render the original numerical vector, not its proper
encoding. `renderWith_respects` handles the actual long rows directly; this is
not positive-cap transport at bottom. The scalar fibres and LOW predicate are
unchanged.
-/

namespace VaughtConjecture.Knight.LowOnly.Family
open  Value ExtOrd CappedDonor 
open LadderScalarRendering RelativeLadderLayer ReceivingCatalogueRanks
noncomputable section
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

/-- Terminal insertion preserves every field rank, including literal tops.
Only membership at the source's own birth grade is asserted. -/
theorem exists_rank_anchor {j} (hj : 1 ≤ j) {S}
    (hs : F.Admissible j S) :
    ∃ a : F.Anchor j, ∀ d, fieldRank a.val d = fieldRank S.profile d := by
  let l := S.freshFloor 0
  have hl : limitPart l = l := S.freshFloor_limit 0
  let β : ExtOrd := ofOrd (l + j)
  have hv : SelfVis j β := by
    rw [selfVis_ofOrd_iff]
    have h := finitePart_limitPart_add_nat l j
    rw [hl] at h
    exact h.ge
  have hb : β ≠ ⊥ := ofOrd_ne_bot _
  let S₀ := S.map (fun x => min x β)
  have hs₀ : F.Admissible j S₀ :=
    hs.map F (capWitness hv hb) hj (capWitness_reflects_bottom hb)
  have hp : AvoidsValue S₀.profile ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun h => ofOrd_ne_top _ (min_eq_top.mp h).2
  have hi d : collapseBlock l (min (S.profile d) β) = S.profile d :=
    collapseBlock_min (ofOrd_le_ofOrd.mpr le_self_add) (S.profile_lt_freshFloor 0 d)
  have hc := collapseBlock_witness j hl
  have hr (d) : fieldRank S₀.profile d = fieldRank S.profile d := by
    have he : S₀.profile = fun d => min (S.profile d) β :=
      funext (State.profile_map _ S)
    rw [he]
    exact fieldRank_of_leftInverse S.profile (fun _ _ h => min_le_min_right _ h)
      hc.mono (min_bot_left _) hc.bot hi d
  let Q := S₀.normalize j
  refine ⟨⟨Q.profile, normalize_inventory j hp, Q, F.normalize_admissible hj hs₀, rfl⟩, ?_⟩
  intro d
  have he : Q.profile = PairedSlotEncoding.normalize j S₀.profile :=
    funext (State.profile_normalize j S₀)
  exact (congrArg (fun p => fieldRank p d) he).trans
    ((fieldRank_normalize hp).trans (hr d))

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : AvoidsValue D.scope A)
  (hboundary : ∀ S : State P C, F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))

include hboundary in
/-- Any admitted numerical vector has a lawful physical rendering with exact
old-field readback. The top ceiling fills every unused rung. -/
theorem exists_physical_section {S} (hs : F.Admissible 1 S) :
    ∃ w ,
      RespectsSemanticsBelow (rows D sem hA field (F.fields 1) hproper) (A, 1) w ∧
      ∀ d : D.below (A, 1), w ⟨old D hA d.1, by rw [old_index]; exact d.2⟩ =
        S.profile (field d.1) := by
  obtain ⟨a, ha⟩ := F.exists_rank_anchor (by decide) hs
  have hr (d) : ranks (F.fields 1) a d = fieldRank S.profile d := ha d
  refine ⟨fun d => renderWith D hA field (F.fields 1) a S.profile ⊤ d.1,
    renderWith_respects D sem hA field (F.fields 1) hproper a S.profile hr
      (fun _ => le_top) (hs.profile_visible_one F) (extVisibilityReplace_top)
      (hboundary S hs), ?_⟩
  intro d
  exact renderWith_old hA field hr

end
end VaughtConjecture.Knight.LowOnly.Family

namespace VaughtConjecture.Knight.LowOnlyOrderedLadder
open  Value ExtOrd CappedDonor LowOnly RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)

include hroot in
/-- Independent physical private supply, including literal top. No ambient,
positive-cap transport, or unfinished-output bountifulness is used. -/
theorem private_bottom_supply (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 1) p) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper hB hC)) (A, 1) w ∧
      ∀ d, w (Family.privateAt F I.boundary hA (privateIncl I) d) = p d := by
  obtain ⟨S, hs, he, _, _⟩ := F.private_bottom_supply hp
  obtain ⟨w, hw, hr⟩ := F.exists_physical_section I.boundary I.rows hA (field I)
    (proper hB hC) (boundary_lawful I F hroot) hs
  refine ⟨w, hw, fun d => ?_⟩
  exact (hr (privateIncl I d)).trans
    ((field_private hroot hs d.1).trans (congrFun he d))

def donorIncl (d : I.left.scheme.below (effC n 1)) : I.boundary.below (A, 1) :=
  ⟨I.leftFace.map d.1,
    I.boundary.scope_subset _, by
      have hg := congrArg Prod.snd (I.leftFace.index d.1)
      change I.boundary.grade (I.leftFace.map d.1) = I.left.scheme.grade d.1 at hg
      exact hg.le.trans (d.2.2.trans (min_le_left _ _))⟩

include hroot in
/-- Donor bottom supply consumes the donor scalar fibre, without exchanging the
two faces in the asymmetric LOW predicate. -/
theorem donor_bottom_supply (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 1) p) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper hB hC)) (A, 1) w ∧
      ∀ d, w ⟨old I.boundary hA (donorIncl I d).1,
        by rw [old_index]; exact (donorIncl I d).2⟩ = p d := by
  obtain ⟨S, hs, he, _, _⟩ := F.donor_bottom_supply hp
  obtain ⟨w, hw, hr⟩ := F.exists_physical_section I.boundary I.rows hA (field I)
    (proper hB hC) (boundary_lawful I F hroot) hs
  refine ⟨w, hw, fun d => ?_⟩
  exact (hr (donorIncl I d)).trans ((field_read I).trans
    ((I.paste_left S.u S.v d.1).trans (congrFun he d)))

include hroot in
/-- All permitted original caps on this grade-one private lifting pair. Every
actual auxiliary receipt is retained; bottom supply is independent. -/
theorem private_lift (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p}
    {q : (carrier I.boundary hA
      (X := Field I.left I.right) (Q := F.Anchor 1)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper hB hC)) (A, 1) q)
    {γ} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (Family.privateAt F I.boundary hA (privateIncl I) d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper hB hC)) (A, 1) w ∧
      (∀ d, w (Family.privateAt F I.boundary hA (privateIncl I) d) = p d) ∧
      CappedEq w q γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨w, hw, hr⟩ := private_bottom_supply I F hroot hA hB hC hp
    exact ⟨w, hw, hr, fun _ => by simp  [hz, ]⟩
  · exact private_positive_lift I F hroot hA hB hC hp hq hγ
      (bot_lt_iff_ne_bot.mpr hz) hag

