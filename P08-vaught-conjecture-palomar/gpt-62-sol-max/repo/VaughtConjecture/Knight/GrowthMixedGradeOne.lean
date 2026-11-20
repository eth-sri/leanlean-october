/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthLeafRecognition
public import VaughtConjecture.Knight.GrowthHigherMixedRows
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.GrowthSpareRecognition
public import VaughtConjecture.Knight.ScopeReplicationSemantics
public import VaughtConjecture.Knight.CappedLifting
public import VaughtConjecture.Knight.CappedLiftingUnique

@[expose] public section

namespace VaughtConjecture.Knight.GrowthMixedGradeOne

open AmalgamationPlan Transform Value ExtOrd Growth GrowthHigherSources

open SupportLadderRows LadderScalarRendering SharpWitnessComposition

open GrowthPaddedContract ScopeReplicationCarrier GrowthHigherMixed

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (G : GrowthPaddedIteration.BuildContext A B C R m n J)

local notation "P" => G.tower

local notation "Fld" => Field G.I.right.scheme G.I.left.scheme

local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue G.X 1)

local notation "ranks₁" => RelativeLadderLayer.ranks (fields G.X 1)

local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)

local notation "spare" => SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos G.I)

local notation "Base" => GrowthPaddedContract.base G.I G.X G.attach G.height G.leftProper G.rightProper

local notation "BaseRows" => GrowthPaddedContract.baseRows G.I G.X G.attach G.height G.leftProper G.rightProper

local notation "Carrier" => GrowthReplicatedRows.carrier P

local notation "Rows" => GrowthReplicatedRows.rows P

local notation "eraseP" => GrowthReplicatedRows.erase P

local notation "addedB" => RelativeLadderLayer.added G.I.boundary G.pos

local notation "oldB" => RelativeLadderLayer.old G.I.boundary G.pos

local notation "ladderRow₁" =>
  RelativeLadderLayer.ladderRow G.I.boundary G.pos
    (GrowthOrderedBase.field G.I) (fields G.X 1)

theorem base_added_cell (v : Pt) : CellScheme.cell Base (addedB v) = (A, 1) :=
  RelativeLadderLayer.added_index G.I.boundary G.pos v

/-- Every cell of grade at most one is a base cell. -/
theorem eq_baseMap_of_grade_le_one (c : Cell (P).carrier) (hc : (P).carrier.grade c ≤ 1) :
    ∃ b, c = (P).baseMap b := by
  rcases (P).cases c with h | ⟨_, hg, _⟩
  all_goals omega

/-- Every full-scope grade-one cell is the image of a padded point. -/
theorem eq_added_of_full_one (c : Cell (P).carrier) (hc : (P).carrier.cell c = (A, 1)) :
    ∃ v : Pt, c = (P).baseMap (addedB v) := by
  obtain ⟨b, rfl⟩ := eq_baseMap_of_grade_le_one G c
    (by simp_all)
  rcases RelativeLadderLayer.cell_cases G.I.boundary G.pos b with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exfalso
    apply GrowthOrderedBase.proper G.I G.leftProper G.rightProper d
    exact (congrArg Prod.fst (original_index G d)).symm.trans
      (congrArg Prod.fst hc)
  tauto

variable {G} (W : Cut G)

/-- A padded copy below a padded copy. -/
def ladderBelow (c v : Pt) :
    CellScheme.below Carrier (CellScheme.cell Carrier (ladderAt W.one c).1) :=
  ⟨(ladderAt W.one v).1, by
    rw [ladderAt_index, ladderAt_index]; exact GradedLe.refl _⟩

/-- All replicated ladder columns read the corresponding base column. -/
theorem row_ladder_at (v : Pt) (z : CellScheme.below Carrier (CellScheme.cell Carrier (ladderAt W.one v).1))
    (b : Cell Base) (hz : eraseP z.1 = (P).baseMap b) :
    Semantics.E Rows (ladderAt W.one v).1 z = ladderRow₁ v b := by
  have h := ScopeReplicationCarrier.erase_le (GrowthReplicatedRows.frame P) z.2
  change GradedLe ((P).carrier.cell (eraseP z.1)) ((P).carrier.cell (eraseP (ladderAt W.one v).1)) at h
  have hb : GradedLe (CellScheme.cell Base b) (CellScheme.cell Base (addedB v)) := by
    simpa only [hz, erase_ladderAt, (P).base_index] using h
  exact ((P).rows.E_congr (erase_ladderAt W.one v) hz).trans
    (((P).base_row (addedB v) ⟨b, hb⟩).trans (RelativeLadderLayer.row_added ..))

theorem row_ladder (c v : Pt) :
    Semantics.E Rows (ladderAt W.one c).1 (ladderBelow W c v) = SupportLadderRows.row ranks₁ c v :=
  (row_ladder_at W c _ (addedB v) (erase_ladderAt W.one v)).trans (RelativeLadderLayer.ladderRow_added ..)

theorem row_ladder_original (v : Pt) (z : CellScheme.below Carrier W.one.index) (d : Cell G.I.boundary)
    (hz : eraseP z.1 = original G d) :
    Semantics.E Rows (ladderAt W.one v).1 ⟨z.1, by rw [ladderAt_index]; exact z.2⟩ =
      SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
        (ranks₁ (SupportLadderRows.parent v) (GrowthOrderedBase.field G.I d)) :=
  (row_ladder_at W v _ (oldB d) hz).trans (RelativeLadderLayer.ladderRow_old ..)

variable {p : CellScheme.below (GrowthHigherMixed.carrier G) W.one.index → ExtOrd}

theorem ladder_lawful (hp : RespectsSemanticsBelow Rows W.one.index p) :
    Lawful ranks₁ (fun v => p (ladderAt W.one v)) := by
  constructor
  · intro v
    have hv := hp.orderly (ladderAt W.one v)
    change p _ = extVisibilityReplace (p _) (CellScheme.cell Carrier _).2
      (CellScheme.cell Carrier _).2 at hv
    rw [ladderAt_index] at hv
    exact hv.symm
  · intro c
    have ht := (hp.locality (ladderAt W.one c)).reindex
      (ladderBelow W c)
    exact transformsTo_congr
      (funext fun v => congrArg Prod.snd (ladderAt_index W.one v))
      (funext fun v => row_ladder W c v) rfl ht

variable (p)

/-- The maximum of `p` over the copies at `U` of the spare rungs. -/
def spareSup : ExtOrd :=
  (Finset.univ : Finset (Catalogue G.X 1)).sup fun b =>
    p (ladderAt W.one (spare b))

variable {p}

theorem ladder_le_spareSup (hp : RespectsSemanticsBelow Rows W.one.index p) (v : Pt) :
    p (ladderAt W.one v) ≤ spareSup W p :=
  ((ladder_lawful W hp).le_parent
    (GrowthLeafRecognition.rank_le_rungs G.I G.X) (GrowthLeafRecognition.rungs_pos G.I) v).trans
    (Finset.le_sup (f := fun b => p (ladderAt W.one (spare b)))
      (Finset.mem_univ _))

/-- Availability bounds every grade-one value at `U` by the spare maximum. -/
theorem grade_one_le (hp : RespectsSemanticsBelow Rows W.one.index p)
    (z : CellScheme.below Carrier W.one.index) (hz : CellScheme.grade Carrier z.1 = 1) :
    p z ≤ spareSup W p := by
  let a₀ := GrowthLeafRecognition.zeroMember G.I G.X 1 le_rfl
  obtain ⟨w, hw, hzw⟩ := hp.availability z (ladderAt W.one (spare a₀))
    (by change CellScheme.scope Carrier z.1 ⊆ (CellScheme.cell Carrier _).1
        rw [ladderAt_index]; exact z.2.1)
    (hz.trans (congrArg Prod.snd (ladderAt_index W.one _)).symm)
  have hw' := hw.trans (ladderAt_index W.one _)
  have hei := ScopeReplicationCarrier.erase_index (GrowthReplicatedRows.frame P) W.mixed w.1 hw'
  obtain ⟨v, hv⟩ := eq_added_of_full_one G _ hei
  have he : p w = p (ladderAt W.one v) :=
    GrowthReplicatedRows.copy_eq P hp w _
      (by change (CellScheme.cell Carrier w.1).1 ⊆ (CellScheme.cell Carrier _).1
          rw [hw', ladderAt_index])
      (hv.trans (erase_ladderAt W.one v).symm)
  exact hzw.trans (he.trans_le (ladder_le_spareSup W hp v))

/-- The chart at a maximal spare point reads the ladder and present originals. -/
structure SpareChart (p : (GrowthHigherMixed.carrier G).below W.one.index → ExtOrd) where
  a : Catalogue G.X 1
  read : ExtOrd → ExtOrd
  witness : Witness (gTop 1) read
  maximum : p (ladderAt W.one (spare a)) = spareSup W p
  bound : ∀ x, read x ≤ spareSup W p
  ladder : ∀ v : Pt, read (SupportLadderRows.row ranks₁ (spare a) v) = p (ladderAt W.one v)
  original : ∀ (z : (GrowthHigherMixed.carrier G).below W.one.index) (d : Cell G.I.boundary),
    eraseP z.1 = GrowthHigherMixed.original G d →
    read (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field G.I d))) = p z

theorem exists_spare_chart (hp : RespectsSemanticsBelow Rows W.one.index p) :
    Nonempty (SpareChart W p) := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Catalogue G.X 1))
    (fun b => p (ladderAt W.one (spare b)))
    ⟨GrowthLeafRecognition.zeroMember G.I G.X 1 le_rfl, Finset.mem_univ _⟩
  let c := ladderAt W.one (spare a)
  have hpc : p c = spareSup W p :=
    le_antisymm (Finset.le_sup (f := fun b => p (ladderAt W.one (spare b)))
      (Finset.mem_univ a)) (Finset.sup_le hmax)
  obtain ⟨τ, hτ, hb, hr⟩ := hp.rowWitness c
  have hgrade : CellScheme.grade Carrier c.1 = 1 :=
    congrArg Prod.snd (ladderAt_index W.one _)
  refine ⟨⟨a, τ, hgrade ▸ hτ, hpc, fun x => (hb x).trans_eq hpc, ?_, ?_⟩⟩
  · intro v
    have h := hr (ladderBelow W (spare a) v)
    rw [row_ladder] at h
    exact h.trans (min_eq_left
      ((ladder_le_spareSup W hp v).trans_eq hpc.symm))
  · intro z d hz
    have hg : CellScheme.grade Carrier z.1 = 1 := by
      have h1 : CellScheme.grade Carrier z.1 ≤ 1 := z.2.2
      have h2 := CellScheme.grade_pos Carrier z.1
      omega
    let e : CellScheme.below Carrier (CellScheme.cell Carrier c.1) :=
      ⟨z.1, by rw [ladderAt_index]; exact z.2⟩
    have h := hr e
    rw [row_ladder_original W (spare a) z d hz,
      SupportLadderRows.ceiling_leaf] at h
    exact h.trans (min_eq_left
      ((grade_one_le W hp z hg).trans_eq hpc.symm))

namespace SpareChart

variable {W} (Ch : SpareChart W p)

/-- **Uncapped complete-field recognition at `U`**, on every field. -/
theorem shadowSup_eq_spare (f : Fld) :
    shadowSup W.one p f =
      Ch.read (SupportLadderRows.source rungs (ranks₁ Ch.a f)) := by
  have he := SupportLadderRows.readout_image (H := rungs)
    (GrowthLeafRecognition.rank_le_rungs G.I G.X) Ch.a (SupportLadderRows.source_mono rungs) f
  simp only [SupportLadderRows.readout] at he
  rw [show Fintype.ofFinite (Catalogue G.X 1) = (inferInstance : Fintype (Catalogue G.X 1)) from
    Subsingleton.elim _ _] at he
  rw [← he, Finset.apply_sup_eq_sup_comp_of_linearOrder Ch.read Ch.witness.mono Ch.witness.bot, shadowSup]
  congr 1
  funext b
  rw [Function.comp_apply, ← Ch.ladder, GrowthSpareRecognition.row_spare]
  rfl

/-- **Finite bottom reflection** on every ladder value of the maximal spare, when `M₁ p ≠ ⊥`. -/
theorem bottom_reflection (hp : RespectsSemanticsBelow Rows W.one.index p)
    (hne : spareSup W p ≠ ⊥) (v : Pt) :
    Ch.read (SupportLadderRows.row ranks₁ (spare Ch.a) v) = ⊥ ↔
      SupportLadderRows.row ranks₁ (spare Ch.a) v = ⊥ := by
  have : Nonempty (Catalogue G.X 1) := ⟨GrowthLeafRecognition.zeroMember G.I G.X 1 le_rfl⟩
  have hread' (w : Pt) : Ch.read (SupportLadderRows.row ranks₁ (spare Ch.a) w) =
      min (p (ladderAt W.one w)) (spareSup W p) := by
    rw [Ch.ladder, min_eq_left (by solve_by_elim [ladder_le_spareSup])]
  have hdiag : Ch.read (SupportLadderRows.row ranks₁ (spare Ch.a) (spare Ch.a)) =
      spareSup W p := (Ch.ladder _).trans Ch.maximum
  exact SupportLadderRows.bottom_reflection (GrowthLeafRecognition.rank_le_rungs G.I G.X)
    (GrowthLeafRecognition.rungs_pos G.I) (by solve_by_elim [ladder_lawful])
    (spare Ch.a) Ch.witness.bot hne hread' hdiag v

end SpareChart

/-- **Exact readback of present originals at `U`**: uncapped. -/
theorem original_readback_one (hp : RespectsSemanticsBelow Rows W.one.index p)
    (z : CellScheme.below Carrier W.one.index) (d : Cell G.I.boundary)
    (hz : eraseP z.1 = original G d) :
    p z = shadowSup W.one p (GrowthOrderedBase.field G.I d) := by
  obtain ⟨Ch⟩ := exists_spare_chart W hp
  exact (Ch.original z d hz).symm.trans (Ch.shadowSup_eq_spare _).symm

namespace SpareChart

variable {W} (Ch : SpareChart W p)

/-- The chart transports the spare's whole ladder row on the padded base. -/
theorem base_section_lawful (hp : RespectsSemanticsBelow Rows W.one.index p) :
    RespectsSemanticsBelow BaseRows (A, 1) (fun d => Ch.read (ladderRow₁ (spare Ch.a) d.1)) := by
  have hlad := RelativeLadderLayer.ladder_respects G.I.boundary G.I.rows
    G.pos (GrowthOrderedBase.field G.I) (fields G.X 1)
    (GrowthOrderedBase.proper G.I G.leftProper G.rightProper) (GrowthOrderedBase.anchor_lawful G.I G.X G.attach) (spare Ch.a)
  by_cases hne : spareSup W p = ⊥
  · have hz : ∀ x, Ch.read x = ⊥ := fun x => le_bot_iff.mp ((Ch.bound x).trans_eq hne)
    simp only [hz]
    apply respectsBelow_bot
  · refine map_respects_of_bottom_reflection hlad (fun d => d.2.2) (Ch.witness.bounded)
      fun d => ?_
    rcases RelativeLadderLayer.cell_cases G.I.boundary G.pos d.1 with
      ⟨e, he⟩ | ⟨v, hv⟩
    · rw [he, GrowthSpareRecognition.ladderRow_spare_old G.I G.X G.height Ch.a e,
        ← GrowthLeafRecognition.index_shadow_self G.I G.X Ch.a, ← GrowthSpareRecognition.row_spare G.I G.X Ch.a]
      exact Ch.bottom_reflection hp hne _
    · rw [hv, GrowthSpareRecognition.ladderRow_spare_added G.I G.X G.height Ch.a v]
      exact Ch.bottom_reflection hp hne _

/-- The extension's values on the installed layer: the chart's reading of the spare's row at
base cells, `⊥` elsewhere (no other cell lies below grade one). -/
def layerSection (c : Cell (P).carrier) : ExtOrd := by
  classical
  exact if h : ∃ b, c = (P).baseMap b then Ch.read (ladderRow₁ (spare Ch.a) h.choose) else ⊥

theorem layerSection_baseMap (b : Cell Base) :
    Ch.layerSection ((P).baseMap b) = Ch.read (ladderRow₁ (spare Ch.a) b) := by
  classical
  unfold layerSection
  split_ifs with h
  · exact congrArg (fun x => Ch.read (ladderRow₁ (spare Ch.a) x)) ((P).base_mono.injective h.choose_spec.symm)
  tauto

/-- The layer section is lawful through grade one on the installed layer. -/
theorem layerSection_lawful (hp : RespectsSemanticsBelow Rows W.one.index p) :
    RespectsSemanticsBelow (P).rows (A, 1) (fun d => Ch.layerSection d.1) := by
  have hbase := Ch.base_section_lawful hp
  have h := (P).base_respects (addedB (spare Ch.a)) (Ch.layerSection)
  have hrhs : RespectsSemanticsBelow BaseRows (CellScheme.cell Base (addedB (spare Ch.a)))
      (fun d => Ch.layerSection ((P).baseMap d.1)) := by
    have hc := GradeCutLayerRows.cast_respects Base BaseRows
      (base_added_cell G (spare Ch.a)).symm hbase
    have he : (fun d : CellScheme.below Base (CellScheme.cell Base (addedB (spare Ch.a))) =>
        Ch.read (ladderRow₁ (spare Ch.a) d.1)) =
        fun d => Ch.layerSection ((P).baseMap d.1) :=
      funext fun d => (Ch.layerSection_baseMap d.1).symm
    rwa [← he]
  have hlhs := h.mpr hrhs
  have hc := GradeCutLayerRows.cast_respects (P).carrier (P).rows (ladder_index G (spare Ch.a)) hlhs
  exact hc

end SpareChart

end

end VaughtConjecture.Knight.GrowthMixedGradeOne
