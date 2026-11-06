
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthOrderedBase
import VaughtConjecture.Knight.ReceivingCatalogueRanks

/-! # Independent physical supply on the growth padded base

As in `LowOnlyGradeOneSupply`, terminal insertion retains complete field ranks,
then the actual numerical table is rendered on the installed anchor. Long-row
lawfulness is proved directly, not by positive-cap transport at bottom.
-/

namespace VaughtConjecture.Knight.Growth
open  Value ExtOrd  
open LadderScalarRendering ReceivingCatalogueRanks
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

theorem exists_rank_anchor {j} (hj : 1 ≤ j) {S}
    (hs : Admitted X j S) :
    ∃ a : Catalogue X j, ∀ d, fieldRank a.val d = fieldRank S.profile d := by
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
  have hs₀ : Admitted X j S₀ :=
    hs.map X (capWitness hv hb) hj (capWitness_reflects_bottom hb)
  have hp : AvoidsValue S₀.profile ⊤ := by
    intro d
    rw [State.profile_map]
    exact fun h => ofOrd_ne_top _ (min_eq_top.mp h).2
  have hi d : collapseBlock l (min (S.profile d) β) = S.profile d :=
    collapseBlock_min (ofOrd_le_ofOrd.mpr le_self_add) (S.profile_lt_freshFloor 0 d)
  have hc := collapseBlock_witness j hl
  have hr (d) : fieldRank S₀.profile d = fieldRank S.profile d := by
    have he : S₀.profile = fun d => min (S.profile d) β := funext (State.profile_map _ S)
    rw [he]
    exact fieldRank_of_leftInverse S.profile (fun _ _ h => min_le_min_right _ h)
      hc.mono (min_bot_left _) hc.bot hi d
  let U := S₀.normalize j
  refine ⟨⟨U.profile, normalize_inventory j hp, U, normalize_admitted X hj hs₀, rfl⟩, ?_⟩
  intro d
  have he : U.profile = PairedSlotEncoding.normalize j S₀.profile :=
    funext (State.profile_normalize j S₀)
  exact (congrArg (fun p => fieldRank p d) he).trans
    ((fieldRank_normalize hp).trans (hr d))

end
end VaughtConjecture.Knight.Growth

namespace VaughtConjecture.Knight.GrowthOrderedBase
open  Value ExtOrd AmalgamationPlan Growth RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev scheme := carrier I.boundary hA
  (X := Field I.right.scheme I.left.scheme) (Q := Catalogue X 1)
abbrev semantics := rows I.boundary I.rows hA (field I) (fields I X) (proper hB hC)

local notation "below₀" => I.boundary.below (A, 1)

def privateIncl (d : I.right.scheme.below (Finset.univ, 1)) : below₀ :=
  ⟨I.rightFace.map d.1,
    I.boundary.scope_subset _,
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans d.2.2⟩

def donorIncl (d : I.left.scheme.below (Finset.univ, 1)) : below₀ :=
  ⟨I.leftFace.map d.1,
    I.boundary.scope_subset _,
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans d.2.2⟩

def oldAt (d : below₀) : (scheme I X hA).below (A, 1) :=
  ⟨old I.boundary hA d.1, by rw [old_index]; exact d.2⟩
abbrev privateAt d := oldAt I X hA (privateIncl I d)
abbrev donorAt d := oldAt I X hA (donorIncl I d)

include T in
theorem exists_physical_section {S}
    (hs : Admitted X 1 S) :
    ∃ w ,
      RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d , w (oldAt I X hA d) = S.profile (field I d.1) := by
  obtain ⟨a, ha⟩ := exists_rank_anchor X (by decide) hs
  refine ⟨fun d => renderWith I.boundary hA (field I) (fields I X) a S.profile ⊤ d.1,
    renderWith_respects I.boundary I.rows hA (field I) (fields I X) (proper hB hC)
      a S.profile ha (fun _ => le_top) hs.visible (extVisibilityReplace_top)
      (boundary_lawful I X T hs), ?_⟩
  intro d
  exact renderWith_old hA (field I) ha

include T in
theorem private_bottom_supply {p}
    (hp : RespectsSemanticsBelow I.right.rows (Finset.univ, 1) p) :
    ∃ w, RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d, w (privateAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.private_all (zero_admitted X) hp
    (selfVis_bot) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (privateIncl I d)).trans
    ((field_private T hs d.1).trans (he d))⟩

include T in
theorem donor_bottom_supply (hN : 1 < X.req.N)
    {p}
    (hp : RespectsSemanticsBelow I.left.rows (Finset.univ, 1) p) :
    ∃ w, RespectsSemanticsBelow (semantics I X hA hB hC) (A, 1) w ∧
      ∀ d, w (donorAt I X hA d) = p d := by
  obtain ⟨S, hs, he, _, _, _⟩ := T.donor_before hN (zero_admitted X) hp
    (selfVis_bot) (fun _ => by simp)
  obtain ⟨w, hw, hr⟩ := exists_physical_section I X T hA hB hC hs
  exact ⟨w, hw, fun d => (hr (donorIncl I d)).trans
    ((field_donor I).trans (he d))⟩

