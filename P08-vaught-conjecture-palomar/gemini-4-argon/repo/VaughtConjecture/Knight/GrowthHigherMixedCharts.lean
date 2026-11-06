/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedRows

/-! # Actual higher-owner charts and decreasing grade maxima

The row identities are consumed on an arbitrary lawful mixed prescription.
Each owner's own locality reads the complete shadow vector capped at that
owner. Its actual lower ceiling occurrences force the bounds needed for a
grade-dependent original projection. No cross-grade rendering equality occurs.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthHigherMixed
open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources GrowthPaddedContract GrowthPaddedIteration SupportLadderRows

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (t : ℕ) (ht : t + 2 ≤ A.card)
local notation "P" => tower I X T hA hB hC t ht
local notation "Pcar" => Layer.carrier (tower I X T hA hB hC t ht)
local notation "Pscope" => CellScheme.scope (Layer.carrier (tower I X T hA hB hC t ht))
local notation "Pgrade" => CellScheme.grade (Layer.carrier (tower I X T hA hB hC t ht))
local notation "Pbelow" => CellScheme.below (Layer.carrier (tower I X T hA hB hC t ht))
local notation "Pcell" => CellScheme.cell (Layer.carrier (tower I X T hA hB hC t ht))
local notation "PE" => Semantics.E (Layer.rows (tower I X T hA hB hC t ht))
local notation "PE_congr" => Semantics.E_congr (Layer.rows (tower I X T hA hB hC t ht))
local notation "D" => carrier I X T hA hB hC t ht
local notation "Dbelow" => CellScheme.below (carrier I X T hA hB hC t ht)
local notation "Dcell" => CellScheme.cell (carrier I X T hA hB hC t ht)
local notation "Dgrade" => CellScheme.grade (carrier I X T hA hB hC t ht)
local notation "Rows" => rows I X T hA hB hC t ht
local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "erase'" => erase I X T hA hB hC t ht

variable (U : Finset ι) (hU : U ∈ R)
  (hm : U = A ∨ ScopeReplicationCarrier.Mixed B C U)
  (j : ℕ) (hj : j ≤ U.card) (hj0 : 1 ≤ j)
  {p : CellScheme.below (carrier I X T hA hB hC t ht) (U, j) → ExtOrd}

local notation "place'" => place I X T hA hB hC t ht U hU hm j hj
local notation "placeIdx'" => place_index I X T hA hB hC t ht U hU hm j hj
local notation "erasePlace'" => erase_place I X T hA hB hC t ht U hU hm j hj
local notation "shadSup'" => shadowSup I X T hA hB hC t ht U hU hm j hj hj0

def nativeArgument (c : Cell Pcar) (hc : Pscope c = A)
    (z : Dbelow (U, j)) (hz : Dgrade z.1 ≤ Pgrade c) : Pbelow (Pcell c) :=
  ⟨erase' z.1,
    (CellScheme.isPlan Pcar).subset_of_mem (CellScheme.scope_mem_plan Pcar _) |>.trans hc.symm.le,
    (ScopeReplicationCarrier.erase_grade Pcar B C z.1).le.trans hz⟩

local notation "natArg" => nativeArgument I X T hA hB hC t ht U j

theorem exists_owner_chart (hp : RespectsSemanticsBelow Rows (U, j) p)
    (c : Cell Pcar) (hc : Pscope c = A) (hg : Pgrade c ≤ j) :
    ∃ τ : ExtOrd → ExtOrd, Witness (gTop (Pgrade c)) τ ∧
      ∀ (z : Dbelow (U, j)) (hz : Dgrade z.1 ≤ Pgrade c),
        τ (PE c (natArg c hc z hz)) = min (p z) (p (place' c hc hg)) := by
  let q := place' c hc hg
  let self : Dbelow (Dcell q.1) := ⟨q.1, GradedLe.refl _⟩
  obtain ⟨τ, hτ, -, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) (hp.orderly q).symm (hp.locality q)
  have hgrade := congrArg Prod.snd (placeIdx' c hc hg)
  change (Dcell q.1).2 = Pgrade c at hgrade
  refine ⟨τ, hgrade ▸ hτ, fun z hz => ?_⟩
  let d : Dbelow (Dcell q.1) := ⟨z.1, by rw [place_index]; exact ⟨z.2.1, hz⟩⟩
  exact (congrArg τ (PE_congr (erasePlace' c hc hg) rfl :
    Semantics.E Rows q.1 d = PE c (natArg c hc z hz)).symm).trans (hr d)

section Owner
variable (c : Cell (tower I X T hA hB hC t ht).carrier)
  (hc : (tower I X T hA hB hC t ht).carrier.scope c = A)
  (hg : (tower I X T hA hB hC t ht).carrier.grade c ≤ j)
  (O : GrowthPaddedOwnerProvenance.Origin I X T hA hB hC t ht c)
  {τ : ExtOrd → ExtOrd} (hτ : Witness (gTop ((tower I X T hA hB hC t ht).carrier.grade c)) τ)
  (hread : ∀ (z : CellScheme.below (carrier I X T hA hB hC t ht) (U, j))
      (hz : (carrier I X T hA hB hC t ht).grade z.1 ≤
        (tower I X T hA hB hC t ht).carrier.grade c),
    τ ((tower I X T hA hB hC t ht).rows.E c
      (nativeArgument I X T hA hB hC t ht U j c hc z hz)) =
        min (p z) (p (place I X T hA hB hC t ht U hU hm j hj c hc hg)))

include hτ hread in
theorem owner_recognition (f : Fld) :
    τ (fields X (O.birth + 2) O.member f) = min (shadSup' p f) (p (place' c hc hg)) := by
  rw [← O.row_shadow_sup f, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot,
    shadowSup, GrowthLeafRecognition.cap_sup]
  refine Finset.sup_congr rfl fun a _ => ?_
  have hz : Dgrade (ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f)).1 ≤ Pgrade c :=
    (congrArg Prod.snd (ladderAt_index I X T hA hB hC t ht U hU hm j hj hj0 _)).le.trans
      (CellScheme.grade_pos Pcar c)
  exact (congrArg τ (PE_congr rfl
    (erase_ladderAt I X T hA hB hC t ht U hU hm j hj hj0 (shadow a f))).symm).trans (hread _ hz)

include hread in
theorem owner_ceiling : τ (GrowthPaddedNativeRows.ceiling I O.birth) = p (place' c hc hg) := by
  have hz : Dgrade (place' c hc hg).1 ≤ Pgrade c := (congrArg Prod.snd (placeIdx' c hc hg)).le
  have hr := hread (place' c hc hg) hz
  have he : PE c (natArg c hc (place' c hc hg) hz) =
      GrowthPaddedNativeRows.ceiling I O.birth :=
    (PE_congr rfl (erasePlace' c hc hg)).trans O.row_diagonal
  rwa [he, min_self] at hr

end Owner

/-- Maximum over every actual occurrence of this grade, not just selected leaves. -/
def gradeMax (p : Dbelow (U, j) → ExtOrd) (i : ℕ) : ExtOrd := by
  classical
  letI := Fintype.ofFinite (Dbelow (U, j))
  exact (Finset.univ : Finset (Dbelow (U, j))).sup fun z => if Dgrade z.1 = i then p z else ⊥

local notation "gMax" => gradeMax I X T hA hB hC t ht U j

theorem le_gradeMax (p : Dbelow (U, j) → ExtOrd) (i : ℕ)
    (z : Dbelow (U, j)) (hz : Dgrade z.1 = i) : p z ≤ gMax p i := by
  classical
  let _ := Fintype.ofFinite (Dbelow (U, j))
  simpa only [gradeMax, ite_eq_left hz] using
    Finset.le_sup (s := (Finset.univ : Finset (Dbelow (U, j))))
      (f := fun w => if Dgrade w.1 = i then p w else ⊥) (Finset.mem_univ z)

theorem exists_maximal_owner (hp : RespectsSemanticsBelow Rows (U, j) p)
    (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hit : i ≤ t + 2) :
    ∃ (c : Cell Pcar) (hc : Pscope c = A) (hg : Pgrade c = i),
      p (place' c hc (hg.le.trans hij)) = gMax p i := by
  classical
  let _ := Fintype.ofFinite (Dbelow (U, j))
  obtain ⟨c₀, hc₀⟩ := GrowthReplicatedRows.complete_through I X T hA hB hC t ht
    (V := (U, i)) (Plan.mem_gradedPlan.mpr ⟨hU, hi, hij.trans hj⟩) hit
  obtain ⟨Ch⟩ := AmbientGradeCharts.exists_chart hp ⟨⟨c₀, by rw [hc₀]; exact ⟨le_rfl, hij⟩⟩, hc₀⟩
  have he := ScopeReplicationCharts.erase_index Pcar B C
    (GrowthReplicatedRows.proper_covered P) hm Ch.owner.1 Ch.index
  let c := erase' Ch.owner.1
  have hc : Pscope c = A := congrArg Prod.fst he
  have hg : Pgrade c = i := congrArg Prod.snd he
  refine ⟨c, hc, hg, ?_⟩
  have hv := GrowthReplicatedRows.copy_eq P hp Ch.owner (place' c hc (hg.le.trans hij))
    (by change (Dcell Ch.owner.1).1 ⊆ (Dcell _).1; rw [Ch.index, place_index])
    (erasePlace' c hc (hg.le.trans hij)).symm
  refine hv.symm.trans (le_antisymm (le_gradeMax I X T hA hB hC t ht U j p i _ Ch.grade)
    (Finset.sup_le fun z _ => ?_))
  split_ifs with hz
  · exact Ch.dominates z hz
  · exact bot_le

include hU hm hj in
/-- Native lower ceilings force decreasing maxima, including comparison to
grade one. Nothing is inferred from independent selected renderings. -/
theorem gradeMax_antitone (hp : RespectsSemanticsBelow Rows (U, j) p)
    (i k : ℕ) (hi : 1 ≤ i) (hk : 2 ≤ k) (hik : i ≤ k)
    (hkj : k ≤ j) (hkt : k ≤ t + 2) : gMax p k ≤ gMax p i := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj hp
    k (by omega) hkj hkt
  let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc (hk.trans_eq hg.symm)
  obtain ⟨τ, -, hread⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp
    c hc (hg.le.trans hkj)
  have hbirth : Pgrade c = O.birth + 2 := congrArg Prod.snd O.owner_index
  have hic : i ≤ Pgrade c := hik.trans_eq hg.symm
  obtain ⟨d, hd, hv⟩ := O.row_ceiling_at i hi (hic.trans_eq hbirth)
  have hds : Pscope d.1 = A := congrArg Prod.fst hd
  have hdg : Pgrade d.1 = i := congrArg Prod.snd hd
  let z := place' d.1 hds (hdg.le.trans (hik.trans hkj))
  have hzi : Dcell z.1 = (U, i) := (placeIdx' _ _ _).trans (congrArg (fun k => (U, k)) hdg)
  have hzg : Dgrade z.1 ≤ Pgrade c := (congrArg Prod.snd hzi).le.trans hic
  have he : PE c (natArg c hc z hzg) = GrowthPaddedNativeRows.ceiling I O.birth :=
    (PE_congr rfl (erasePlace' _ _ _)).trans hv
  have hr := hread z hzg
  rw [he, owner_ceiling I X T hA hB hC t ht U hU hm j hj c hc (hg.le.trans hkj) O hread] at hr
  exact hmax.symm.le.trans ((min_eq_right_iff.mp hr.symm).trans
    (le_gradeMax I X T hA hB hC t ht U j p i z (congrArg Prod.snd hzi)))

/-- Exact present-original readback at every grade at least two on the fixed
final carrier. Lower values are not clipped to a higher owner's maximum. -/
theorem original_readback (hp : RespectsSemanticsBelow Rows (U, j) p)
    (z : Dbelow (U, j)) (d : Cell I.boundary)
    (hz : erase' z.1 = original I X T hA hB hC t ht d)
    (hg2 : 2 ≤ Dgrade z.1) (hgt : Dgrade z.1 ≤ t + 2) :
    p z = min (shadSup' p (GrowthOrderedBase.field I d)) (gMax p (Dgrade z.1)) := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner I X T hA hB hC t ht U hU hm j hj hp
    (Dgrade z.1) (by omega) z.2.2 hgt
  let O := GrowthPaddedOwnerProvenance.origin I X T hA hB hC t ht c hc (hg2.trans_eq hg.symm)
  obtain ⟨τ, hτ, hread⟩ := exists_owner_chart I X T hA hB hC t ht U hU hm j hj hp
    c hc (hg.le.trans z.2.2)
  have hzc : Dgrade z.1 ≤ Pgrade c := hg.symm.le
  have hdg : I.boundary.grade d ≤ O.birth + 2 := by
    have he : Pgrade (erase' z.1) = Dgrade z.1 :=
      ScopeReplicationCarrier.erase_grade Pcar B C z.1
    rw [hz] at he
    have hb : Pgrade c = O.birth + 2 := congrArg Prod.snd O.owner_index
    exact (congrArg Prod.snd (original_index I X T hA hB hC t ht d)).symm.le.trans
      (he.le.trans (hzc.trans_eq hb))
  have hd : GradedLe (I.boundary.cell d) (A, O.birth + 2) :=
    ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan d), hdg⟩
  have he : min (p z) (p (place' c hc (hg.le.trans z.2.2))) =
      min (shadSup' p (GrowthOrderedBase.field I d)) (p (place' c hc (hg.le.trans z.2.2))) :=
    (hread z hzc).symm.trans ((congrArg τ ((PE_congr rfl hz).trans (O.row_original d hd))).trans
      (owner_recognition I X T hA hB hC t ht U hU hm j hj hj0 c hc (hg.le.trans z.2.2) O hτ hread _))
  rwa [hmax, min_eq_left (le_gradeMax I X T hA hB hC t ht U j p _ z rfl)] at he

