/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthHigherMixedRows

/-! # Actual higher-owner charts and decreasing grade maxima

The row identities are consumed on an arbitrary lawful mixed prescription.
Each owner's own locality reads the complete shadow vector capped at that
owner. Its actual lower ceiling occurrences force the bounds needed for a
grade-dependent original projection. No cross-grade rendering equality occurs.
-/

namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan    Growth GrowthHigherSources
open GrowthPaddedContract  SupportLadderRows
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower I X T hA hB hC t ht
local notation "D" => carrier I X T hA hB hC t ht
local notation "Rows" => rows I X T hA hB hC t ht
local notation "Fld" => Field I.right.scheme I.left.scheme

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

local notation "erase₀" => erase I X T hA hB hC t ht

variable {I X T hA hB hC t ht U j} in
def nativeArgument c (hc : (P).carrier.scope c = A)
    (z : (D).below (U, j)) (hz : (D).grade z.1 ≤ (P).carrier.grade c) :
    (P).carrier.below ((P).carrier.cell c) :=
  ⟨erase₀ z.1,
    ((P).carrier.scope_subset _).trans hc.symm.le,
    (ScopeReplicationCarrier.erase_grade (P).carrier B C z.1).le.trans hz⟩

local notation "erase_place₀" => erase_place hU hm hj

local notation "nativeArgument₀" => nativeArgument

local notation "place_index₀" => place_index hU hm hj

local notation "place₀" => place I X T hA hB hC t ht U hU hm j hj

variable {I X T hA hB hC t ht U j} in
theorem exists_owner_chart (hp : RespectsSemanticsBelow Rows (U, j) p)
    {c : Cell (P).carrier} {hc : (P).carrier.scope c = A} {hg : (P).carrier.grade c ≤ j} :
    ∃ τ , Witness (gTop ((P).carrier.grade c)) τ ∧
      ∀ z hz,
        τ ((P).rows.E c (nativeArgument₀ c hc z hz)) =
          min (p z) (p (place₀ c hc hg)) := by
  let q := place₀ c hc hg
  let self : (D).belowCell q.1 := ⟨q.1, GradedLe.refl _⟩
  obtain ⟨τ, hτ, -, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) (hp.orderly q).symm (hp.locality q)
  have hgrade := congrArg Prod.snd (place_index₀ c hc hg)
  
  
  rw [hgrade] at hτ
  refine ⟨τ, hτ, ?_⟩
  intro z hz
  let d : (D).belowCell q.1 :=
    ⟨z.1, by rw [place_index]; exact ⟨z.2.1, hz⟩⟩
  have he : Semantics.E Rows q.1 d =
      (P).rows.E c (nativeArgument₀ c hc z hz) :=
    (P).rows.E_congr (erase_place₀ c hc hg) rfl
  exact (congrArg τ he.symm).trans (hr d)

section
variable (c : Cell (tower I X T hA hB hC t ht).carrier)
  (hc : (tower I X T hA hB hC t ht).carrier.scope c = A)
  (hg : (tower I X T hA hB hC t ht).carrier.grade c ≤ j)
  (O : GrowthPaddedOwnerProvenance.Origin I X T hA hB hC t ht c)
  {τ : LabelMap} (hτ : Witness (gTop ((tower I X T hA hB hC t ht).carrier.grade c)) τ)
  (hread : ∀ z
      hz,
    τ ((tower I X T hA hB hC t ht).rows.E c
      (nativeArgument c hc z hz)) =
        min (p z) (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)))

include hτ hread in
variable {I X T hA hB hC t ht U hU hm j hj c hc hg} in
theorem owner_recognition f :
    τ (fields X (O.birth + 2) O.member f) =
      min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p f)
        (p (place₀ c hc hg)) := by
  rw [← O.row_shadow_sup f, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot,
    shadowSup, GrowthLeafRecognition.cap_sup]
  apply Finset.sup_congr rfl
  intro a _
  have hz : (D).grade
      (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f)).1 ≤
      (P).carrier.grade c :=
    (congrArg Prod.snd (ladderAt_index I X T hA hB hC t ht U hU hm j hj hj0 _)).le.trans
      ((P).carrier.grade_pos c)
  exact (congrArg τ ((P).rows.E_congr rfl
    (erase_ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f))).symm).trans
      (hread _ hz)

include hread in
def owner_ceiling := by
  have hz  :=
    (congrArg Prod.snd (place_index₀ c hc hg)).le
  have hr := hread (place₀ c hc hg) hz
  have he : (P).rows.E c (nativeArgument₀ c hc
      (place₀ c hc hg) hz) =
        GrowthPaddedNativeRows.ceiling I O.birth :=
    ((P).rows.E_congr rfl (erase_place₀ c hc hg)).trans
      O.row_diagonal
  rw [he, min_self] at hr
  exact hr

include O hread in
/-- An actual earlier-grade occurrence, not just a numerical height bound. -/
theorem exists_lower_dominator i (hi : 1 ≤ i) (hic : i ≤ (P).carrier.grade c) :
    ∃ d , (D).cell d.1 = (U, i) ∧
      p (place₀ c hc hg) ≤ p d := by
  have hbirth := congrArg Prod.snd O.owner_index
  
  obtain ⟨d, hd, hv⟩ := O.row_ceiling_at i hi (hic.trans_eq hbirth)
  have hds  := congrArg Prod.fst hd
  have hdg  := congrArg Prod.snd hd
  let z := place₀ d.1 hds (hdg.le.trans (hic.trans hg))
  have hzi : (D).cell z.1 = (U, i) :=
    (place_index₀ _ _ _).trans
      (congrArg (fun k => (U, k)) hdg)
  have hzg  := (congrArg Prod.snd hzi).le.trans hic
  have he : (P).rows.E c (nativeArgument₀ c hc z hzg) =
      GrowthPaddedNativeRows.ceiling I O.birth :=
    ((P).rows.E_congr rfl (erase_place₀ _ _ _)).trans hv
  have hr := hread z hzg
  rw [he, owner_ceiling I X T hA hB hC t ht U hU hm j hj c hc hg O hread] at hr
  exact ⟨z, hzi, min_eq_right_iff.mp hr.symm⟩

include O hτ hread in
def owner_original_readback (z : (D).below (U, j)) d
    (hz : erase₀ z.1 = original I X T hA hB hC t ht d)
    (hzc : (D).grade z.1 ≤ (P).carrier.grade c) := by
  have hdg  := by
    have he := ScopeReplicationCarrier.erase_grade (P).carrier B C z.1
    change (P).carrier.grade (erase₀ z.1) = (D).grade z.1 at he
    rw [hz] at he
    have hi := congrArg Prod.snd (original_index T hA hB hC ht d)
    have hb := congrArg Prod.snd O.owner_index
    
    exact hi.symm.le.trans (he.le.trans (hzc.trans_eq hb))
  have hd : GradedLe (I.boundary.cell d) (A, O.birth + 2) :=
    ⟨I.boundary.scope_subset d, hdg⟩
  have he : (P).rows.E c (nativeArgument₀ c hc z hzc) =
      fields X (O.birth + 2) O.member (GrowthOrderedBase.field I d) :=
    ((P).rows.E_congr rfl hz).trans (O.row_original d hd)
  exact (hread z hzc).symm.trans ((congrArg τ he).trans
    (owner_recognition hj0 O hτ hread _))

end

/-- Maximum over every actual occurrence of this grade, not just selected leaves. -/
def gradeMax (p : (D).below (U, j) → ExtOrd) (i : ℕ) : ExtOrd := by
  
  letI := Fintype.ofFinite ((D).below (U, j))
  exact (Finset.univ).sup fun z =>
    if (D).grade z.1 = i then p z else ⊥

local notation "gradeMax₀" => gradeMax I X T hA hB hC t ht U j

variable {I X T hA hB hC t ht U j} in
theorem le_gradeMax (p : (D).below (U, j) → ExtOrd) (i : ℕ)
    (z : (D).below (U, j)) (hz : (D).grade z.1 = i) :
    p z ≤ gradeMax₀ p i := by
  classical
  let _ := Fintype.ofFinite ((D).below (U, j))
  have h := Finset.le_sup 
    (f := fun w => if (D).grade w.1 = i then p w else ⊥) (Finset.mem_univ z)
  simpa only [gradeMax, ite_eq_left hz] using h

local notation "le_gradeMax₀" => le_gradeMax p

def chart_gradeMax {i : ℕ} (Ch : AmbientGradeCharts.Chart Rows (U, j) p i) := by
  classical
  
  refine le_antisymm (le_gradeMax₀ i _ Ch.grade) ?_
  apply Finset.sup_le
  intro z _
  split_ifs with hz
  · exact Ch.dominates z hz
  · exact bot_le

include hU hj in
theorem exists_grade_chart (hp : RespectsSemanticsBelow Rows (U, j) p)
    i (hi : 1 ≤ i) (hij : i ≤ j) (hit : i ≤ t + 2) :
    Nonempty (AmbientGradeCharts.Chart Rows (U, j) p i) := by
  obtain ⟨c, hc⟩ := GrowthReplicatedRows.complete_through I X T hA hB hC t ht
    (V := (U, i)) (Plan.mem_gradedPlan.mpr ⟨hU, hi, hij.trans hj⟩) hit
  exact AmbientGradeCharts.exists_chart hp
    ⟨⟨c, by rw [hc]; exact ⟨le_rfl, hij⟩⟩, hc⟩

variable {I X T hA hB hC t ht U j} in
theorem exists_maximal_owner (hp : RespectsSemanticsBelow Rows (U, j) p)
    (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hit : i ≤ t + 2) :
    ∃ (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
      (hg : (P).carrier.grade c = i),
      p (place₀ c hc (hg.le.trans hij)) =
        gradeMax₀ p i := by
  obtain ⟨Ch⟩ := exists_grade_chart I X T hA hB hC t ht U hU j hj hp i hi hij hit
  have he := ScopeReplicationCharts.erase_index (P).carrier B C
    (GrowthReplicatedRows.proper_covered P) hm Ch.owner.1 Ch.index
  let c := erase₀ Ch.owner.1
  have hc : (P).carrier.scope c = A := congrArg Prod.fst he
  have hg : (P).carrier.grade c = i := congrArg Prod.snd he
  refine ⟨c, hc, hg, ?_⟩
  have hv := GrowthReplicatedRows.copy_eq P hp
    (by change ((D).cell Ch.owner.1).1 ⊆ ((D).cell _).1
        rw [Ch.index, place_index])
    (erase_place₀ c hc (hg.le.trans hij)).symm
  exact hv.symm.trans (chart_gradeMax I X T hA hB hC t ht U j Ch)

include hU hm hj in
/-- Native lower ceilings force decreasing maxima, including comparison to
grade one. Nothing is inferred from independent selected renderings. -/
theorem gradeMax_antitone (hp : RespectsSemanticsBelow Rows (U, j) p)
    (i k : ℕ) (hi : 1 ≤ i) (hk : 2 ≤ k) (hik : i ≤ k)
    (hkj : k ≤ j) (hkt : k ≤ t + 2) :
    gradeMax₀ p k ≤ gradeMax₀ p i := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner hU hm hj hp
    k (by omega) hkj hkt
  let O := GrowthPaddedOwnerProvenance.origin hc (hk.trans_eq hg.symm)
  obtain ⟨τ, hτ, hr⟩ := exists_owner_chart hU hm hj hp
  obtain ⟨d, hd, hle⟩ := exists_lower_dominator I X T hA hB hC t ht U hU hm j hj
    c hc (hg.le.trans hkj) O hr i hi (hik.trans_eq hg.symm)
  exact hmax.symm.le.trans (hle.trans (le_gradeMax₀ i d
    (congrArg Prod.snd hd)))

/-- Exact present-original readback at every grade at least two on the fixed
final carrier. Lower values are not clipped to a higher owner's maximum. -/
theorem original_readback (hp : RespectsSemanticsBelow Rows (U, j) p)
    (z : (D).below (U, j)) (d : Cell I.boundary)
    (hz : erase₀ z.1 = original I X T hA hB hC t ht d)
    (hg2 : 2 ≤ (D).grade z.1) (hgt : (D).grade z.1 ≤ t + 2) :
    p z = min (shadowSup I X T hA hB hC t ht U hU hm j hj hj0 p (GrowthOrderedBase.field I d))
      (gradeMax₀ p ((D).grade z.1)) := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner hU hm hj hp
    ((D).grade z.1) (by omega) z.2.2 hgt
  let O := GrowthPaddedOwnerProvenance.origin hc (hg2.trans_eq hg.symm)
  obtain ⟨τ, hτ, hr⟩ := exists_owner_chart hU hm hj hp
  have he := owner_original_readback I X T hA hB hC t ht U hU hm j hj hj0
    c hc (hg.le.trans z.2.2) O hτ hr z d hz hg.symm.le
  rw [hmax, min_eq_left (le_gradeMax₀ _ z rfl)] at he
  exact he

