/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthHigherMixedRows

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherMixed

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open GrowthPaddedContract GrowthPaddedIteration SupportLadderRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "D" => carrier G

local notation "Rows" => rows G

local notation "Fld" => Field G.I.right.scheme G.I.left.scheme

variable {G} (W : Cut G)
  {p : CellScheme.below (carrier G) W.index → ExtOrd}

/-- A lawful owner's chart identifies its native row with the observed
replicated occurrences of that row, including all ladder points. -/
structure OwnerChart (p : (D).below W.index → ExtOrd) (c : Cell (P).carrier) where
  full : (P).carrier.scope c = A
  bounded : (P).carrier.grade c ≤ W.grade
  origin : GrowthPaddedOwnerProvenance.Origin G c
  read : ExtOrd → ExtOrd
  witness : Witness (gTop ((P).carrier.grade c)) read
  row : ∀ (z : (D).below W.index) (d : (P).carrier.below ((P).carrier.cell c)),
    erase G z.1 = d.1 → read ((P).rows.E c d) = min (p z) (p (place W c full bounded))

theorem exists_owner_chart (hp : RespectsSemanticsBelow Rows W.index p)
    (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
    (hg : (P).carrier.grade c ≤ W.grade) (h2 : 2 ≤ (P).carrier.grade c) :
    Nonempty (OwnerChart W p c) := by
  let q := place W c hc hg
  obtain ⟨τ, hτ, -, hr⟩ := hp.rowWitness q
  have hgrade := congrArg Prod.snd (place_index W c hc hg)
  change (D).grade q.1 = (P).carrier.grade c at hgrade
  change Witness (gTop ((D).grade q.1)) τ at hτ
  rw [hgrade] at hτ
  refine ⟨⟨hc, hg, GrowthPaddedOwnerProvenance.origin G c hc h2, τ, hτ, ?_⟩⟩
  intro z d he
  have hz := ScopeReplicationCarrier.erase_grade (GrowthReplicatedRows.frame P) z.1
  have hzd : (D).grade z.1 ≤ (P).carrier.grade c := hz.symm.le.trans ((congrArg (P).carrier.grade he).trans_le d.2.2)
  let dz : (D).below ((D).cell q.1) := ⟨z.1, by rw [place_index]; exact ⟨z.2.1, hzd⟩⟩
  exact (congrArg τ ((P).rows.E_congr (erase_place W c hc hg) he).symm).trans (hr dz)

namespace OwnerChart

variable {W} {c : Cell G.tower.carrier} (Ch : OwnerChart W p c)

abbrev point := place W c Ch.full Ch.bounded

local notation "O" => Ch.origin

theorem recognition (f : Fld) : Ch.read (fields G.X ((O).birth + 2) (O).member f) =
    min (shadowSup W p f) (p Ch.point) := by
  rw [← (O).row_shadow_sup f, Finset.apply_sup_eq_sup_comp_of_linearOrder Ch.read Ch.witness.mono
    Ch.witness.bot, shadowSup, GrowthLeafRecognition.cap_sup]
  exact Finset.sup_congr rfl fun a _ => Ch.row _ _ (erase_ladderAt W (shadow a f))

theorem ceiling : Ch.read (O).ceiling = p Ch.point := by
  simpa only [(O).row_diagonal, min_self] using
    Ch.row Ch.point ⟨c, GradedLe.refl _⟩ (erase_place W c Ch.full Ch.bounded)

/-- An actual earlier-grade occurrence dominates the chart's owner. -/
theorem exists_lower_dominator (i : ℕ) (hi : 1 ≤ i) (hic : i ≤ (P).carrier.grade c) :
    ∃ d : (D).below W.index, (D).cell d.1 = (W.scope, i) ∧ p Ch.point ≤ p d := by
  obtain ⟨d, hd, hv⟩ := (O).row_ceiling_at i hi (hic.trans_eq (congrArg Prod.snd (O).owner_index))
  have hds : (P).carrier.scope d.1 = A := congrArg Prod.fst hd
  have hdg : (P).carrier.grade d.1 = i := congrArg Prod.snd hd
  let z := place W d.1 hds (hdg.le.trans (hic.trans Ch.bounded))
  have hr := Ch.row z d (erase_place W _ _ _)
  rw [hv, Ch.ceiling] at hr
  exact ⟨z, (place_index W _ _ _).trans (Prod.ext rfl hdg), min_eq_right_iff.mp hr.symm⟩

theorem original_readback (z : (D).below W.index) (d : Cell G.I.boundary)
    (hz : erase G z.1 = original G d) (hzc : (D).grade z.1 ≤ (P).carrier.grade c) :
    min (p z) (p Ch.point) = min (shadowSup W p (GrowthOrderedBase.field G.I d)) (p Ch.point) := by
  have hg : (P).carrier.grade (erase G z.1) = (D).grade z.1 :=
    ScopeReplicationCarrier.erase_grade (GrowthReplicatedRows.frame P) z.1
  have hd : GradedLe (G.I.boundary.cell d) (A, (O).birth + 2) :=
    ⟨G.I.boundary.scope_subset d, (congrArg Prod.snd (original_index G d)).symm.le.trans
      ((congrArg (P).carrier.grade hz).symm.le.trans (hg.le.trans
        (hzc.trans_eq (congrArg Prod.snd (O).owner_index))))⟩
  have hr := Ch.row z ((O).originalArgument d hd) hz
  rw [(O).row_original, Ch.recognition] at hr
  exact hr.symm

end OwnerChart

/-- Maximum over every actual occurrence of this grade, not just selected leaves. -/
def gradeMax (p : (D).below W.index → ExtOrd) (i : ℕ) : ExtOrd := by
  classical
  letI := Fintype.ofFinite ((D).below W.index)
  exact (Finset.univ : Finset ((D).below W.index)).sup fun z =>
    if (D).grade z.1 = i then p z else ⊥

theorem le_gradeMax (p : (D).below W.index → ExtOrd) (i : ℕ)
    (z : (D).below W.index) (hz : (D).grade z.1 = i) :
    p z ≤ gradeMax W p i := by
  classical
  let _ := Fintype.ofFinite ((D).below W.index)
  have h := Finset.le_sup (s := (Finset.univ : Finset ((D).below W.index)))
    (f := fun w => if (D).grade w.1 = i then p w else ⊥) (Finset.mem_univ z)
  aesop

theorem chart_gradeMax {i : ℕ} (Ch : AmbientGradeCharts.Chart Rows W.index p i) :
    p Ch.owner = gradeMax W p i := by
  classical
  let _ := Fintype.ofFinite ((D).below W.index)
  refine le_antisymm (le_gradeMax W p i _ Ch.grade) ?_
  apply Finset.sup_le
  intro z _
  split_ifs with hz
  · exact Ch.dominates z hz
  simp

theorem exists_grade_chart (hp : RespectsSemanticsBelow Rows W.index p)
    (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ W.grade) :
    Nonempty (AmbientGradeCharts.Chart Rows W.index p i) := by
  obtain ⟨c, hc⟩ := GrowthReplicatedRows.complete_through G
    (V := (W.scope, i)) (Plan.mem_gradedPlan.mpr ⟨W.member, hi, hij.trans W.card⟩) (hij.trans W.installed)
  exact AmbientGradeCharts.exists_chart hp
    ⟨⟨c, by (constructor <;> simp_all)⟩, hc⟩

theorem exists_maximal_owner (hp : RespectsSemanticsBelow Rows W.index p)
    (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ W.grade) :
    ∃ (c : Cell (P).carrier) (hc : (P).carrier.scope c = A)
      (hg : (P).carrier.grade c = i),
      p (place W c hc (hg.le.trans hij)) =
        gradeMax W p i := by
  obtain ⟨Ch⟩ := exists_grade_chart W hp i hi hij
  have he := ScopeReplicationCarrier.erase_index (GrowthReplicatedRows.frame P) W.mixed Ch.owner.1 Ch.index
  let c := erase G Ch.owner.1
  have hc : (P).carrier.scope c = A := congrArg Prod.fst he
  have hg : (P).carrier.grade c = i := congrArg Prod.snd he
  refine ⟨c, hc, hg, ?_⟩
  have hv := GrowthReplicatedRows.copy_eq P hp Ch.owner
    (place W c hc (hg.le.trans hij))
    (by change ((D).cell Ch.owner.1).1 ⊆ ((D).cell _).1
        rw [Ch.index, place_index])
    (erase_place W c hc (hg.le.trans hij)).symm
  exact hv.symm.trans (by solve_by_elim [chart_gradeMax])

/-- Native lower ceilings force decreasing maxima, including comparison to
grade one. Nothing is inferred from independent selected renderings. -/
theorem gradeMax_antitone (hp : RespectsSemanticsBelow Rows W.index p)
    (i k : ℕ) (hi : 1 ≤ i) (hk : 2 ≤ k) (hik : i ≤ k)
    (hkj : k ≤ W.grade) :
    gradeMax W p k ≤ gradeMax W p i := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner W hp
    k (by omega) hkj
  obtain ⟨Ch⟩ := exists_owner_chart W hp c hc (hg.le.trans hkj) (hk.trans_eq hg.symm)
  obtain ⟨d, hd, hle⟩ := Ch.exists_lower_dominator i hi (hik.trans_eq hg.symm)
  exact hmax.symm.le.trans (hle.trans (le_gradeMax W p i d
    (congrArg Prod.snd hd)))

/-- Exact present-original readback at every grade at least two on the fixed
final carrier. Lower values are not clipped to a higher owner's maximum. -/
theorem original_readback (hp : RespectsSemanticsBelow Rows W.index p)
    (z : (D).below W.index) (d : Cell G.I.boundary)
    (hz : erase G z.1 = original G d)
    (hg2 : 2 ≤ (D).grade z.1) :
    p z = min (shadowSup W p (GrowthOrderedBase.field G.I d))
      (gradeMax W p ((D).grade z.1)) := by
  obtain ⟨c, hc, hg, hmax⟩ := exists_maximal_owner W hp
    ((D).grade z.1) (by omega) z.2.2
  obtain ⟨Ch⟩ := exists_owner_chart W hp c hc (hg.le.trans z.2.2) (hg2.trans_eq hg.symm)
  have he := Ch.original_readback z d hz hg.ge
  rw [show p Ch.point = gradeMax W p ((D).grade z.1) from hmax,
    min_eq_left (le_gradeMax W p _ z rfl)] at he
  exact he

end

end VaughtConjecture.Knight.GrowthHigherMixed
