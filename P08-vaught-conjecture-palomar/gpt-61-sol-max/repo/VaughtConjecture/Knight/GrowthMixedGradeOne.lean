
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GrowthLeafRecognition
import VaughtConjecture.Knight.GrowthReplicatedRows
import VaughtConjecture.Knight.ScopeReplicationCharts
import VaughtConjecture.Knight.GrowthSpareRecognition
import VaughtConjecture.Knight.ScopeReplicationRestriction
import VaughtConjecture.Knight.CappedLifting
import VaughtConjecture.Knight.CappedLiftingUnique

/-! # The grade-one mixed case on the replicated growth carrier

On the replicated growth carrier over **any** installed layer `P` (the grade-one lower domain is
the literal padded base on every layer, through `P.baseMap`), for an eligible mixed scope `U`
(`U = A` or `Mixed B C U`, `U` in the plan) and an **arbitrary** lawful section `p` below
`(U, 1)`:

* **Recognition** (`exists_spare_chart`, `shadowSup_eq_spare`, `original_readback_one`): the
  maximal spare copy at `U` carries a chart `τ` through grade one reading every padded copy
  exactly and every present original as the rank-coded source of its field; the uncapped
  complete-field vector `B_p f` is `τ (source rungs (rank_a f))` on every field, present, hidden
  or future.
* **Extension** (`extension`, `extension_lawful`, `extension_original`, `extension_auxiliary`,
  `extension_restrict`): the section `τ ∘ ladderRow (spare a)` on the padded base — hidden
  originals receive their recognized field values, every auxiliary receives the value of its
  actual `U`-copy — is lawful on the base (`RelativeLadderLayer.ladder_respects` transported
  by finite bottom reflection), hence on `P` (`base_respects`), hence duplicated on the whole
  replicated carrier (`ScopeReplicationLifting.duplicate_lawful`); it restricts to `p` literally.
* **Uniqueness** (`eq_of_restriction`): two lawful sections below `(A, 1)` agreeing on the
  `U`-copies agree everywhere: auxiliaries by `ScopeReplicationRestriction.auxiliary_eq`,
  originals through the full-scope recognition of each.
* **The capped lift** (`cappedLift`, `cappedLift_built`): `ExtensionInjectivity` gives
  `CoatomBoundaryExtension.CappedLift` for `(U, 1) ≤ (A, 1)` at every permitted cap, bottom and
  top included, on every installed layer and in particular on every built carrier.

The zero section, literal top, unused rungs and long tips are covered: nothing is assumed of `p`
beyond lawfulness, and no admission or activation hypothesis enters. -/

namespace VaughtConjecture.Knight.GrowthMixedGradeOne

open AmalgamationPlan Transform Value  Growth GrowthHigherSources
open SupportLadderRows  SharpWitnessComposition
open GrowthPaddedContract ScopeReplicationCarrier

noncomputable section

theorem one_le_card {ι} {A B C U : Finset ι} (hA : 2 ≤ A.card)
    (hm : U = A ∨ Mixed B C U) : 1 ≤ U.card := by grind [VaughtConjecture.Knight.ScopeReplicationCarrier.Mixed]

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  {k : ℕ} (P : Layer I X T hA hB hC k)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "spare" => SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I)
local notation "Base" => GrowthPaddedContract.base I X T hA hB hC
local notation "BaseRows" => GrowthPaddedContract.baseRows T hA hB hC
local notation "Carrier" => GrowthReplicatedRows.carrier P
local notation "Rows" => GrowthReplicatedRows.rows P
local notation "eraseP" => GrowthReplicatedRows.erase P
local notation "coverP" => GrowthReplicatedRows.proper_covered P
local notation "addedB" => RelativeLadderLayer.added I.boundary (GrowthLeafRecognition.card_pos hA)
local notation "oldB" => RelativeLadderLayer.old I.boundary (GrowthLeafRecognition.card_pos hA)
local notation "ladderRow₁" =>
  RelativeLadderLayer.ladderRow I.boundary (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1)

/-! ## The grade-one geometry of an installed layer -/

theorem base_added_cell v : CellScheme.cell Base (addedB v) = (A, 1) :=
  RelativeLadderLayer.added_index I.boundary (GrowthLeafRecognition.card_pos hA) v

theorem base_old_cell d : CellScheme.cell Base (oldB d) = I.boundary.cell d :=
  RelativeLadderLayer.old_index d

def carrier_added_cell v :=
  (P.base_index _).trans (base_added_cell I X T hA hB hC v)

def carrier_old_cell d :=
  (P.base_index _).trans (base_old_cell I X T hA hB hC d)

/-- Every cell of grade at most one is a base cell. -/
theorem eq_baseMap_of_grade_le_one c (hc : P.carrier.grade c ≤ 1) :
    ∃ b, c = P.baseMap b := by
  rcases P.cases c with h | ⟨_, hg, _⟩
  · exact h
  · omega

/-- Every full-scope grade-one cell is the image of a padded point. -/
theorem eq_added_of_full_one c (hc : P.carrier.cell c = (A, 1)) :
    ∃ v , c = P.baseMap (addedB v) := by
  obtain ⟨b, rfl⟩ := eq_baseMap_of_grade_le_one I X T hA hB hC P c
    (by simp_all)
  rcases RelativeLadderLayer.cell_cases b with
    ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exfalso
    apply GrowthOrderedBase.proper hB hC d
    exact (congrArg Prod.fst (carrier_old_cell I X T hA hB hC P d)).symm.trans
      (congrArg Prod.fst hc)
  · exact ⟨v, rfl⟩

/-! ## Occurrences at an eligible mixed scope -/

variable (U : Finset ι) (hU : U ∈ P.carrier.plan) (hm : U = A ∨ Mixed B C U)

theorem scope_added v : P.carrier.scope (P.baseMap (addedB v)) = A := by
  change (P.carrier.cell _).1 = A
  rw [carrier_added_cell]

theorem grade_added v : P.carrier.grade (P.baseMap (addedB v)) = 1 := by
  change (P.carrier.cell _).2 = 1
  rw [carrier_added_cell]

include hm in
theorem grade_added_le v : P.carrier.grade (P.baseMap (addedB v)) ≤ U.card := by
  rw [grade_added]; exact one_le_card hA hm

/-- The copy at `U` of a padded point. -/
def ladderAt (v : Pt) : CellScheme.below Carrier (U, 1) :=
  ⟨atScope P.carrier B C U hU hm (P.baseMap (addedB v)) (scope_added I X T hA hB hC P v)
      (grade_added_le I X T hA hB hC P U hm v), by
    rw [atScope_index, grade_added]
    exact GradedLe.refl _⟩

local notation "ladderAt₀" => ladderAt I X T hA hB hC P U hU hm

theorem ladder_index v :
    CellScheme.cell Carrier (ladderAt₀ v).1 = (U, 1) := by
  unfold ladderAt
  rw [atScope_index, grade_added]

theorem erase_ladder v :
    eraseP (ladderAt₀ v).1 = P.baseMap (addedB v) :=
  erase_atScope P.carrier B C U hU hm (P.baseMap (addedB v)) (scope_added I X T hA hB hC P v)
    (grade_added_le I X T hA hB hC P U hm v)

/-- A padded copy below a padded copy. -/
def ladderBelow (c v : Pt) :
    CellScheme.below Carrier (CellScheme.cell Carrier (ladderAt₀ c).1) :=
  ⟨(ladderAt₀ v).1, by
    grind [ladder_index]⟩

local notation "erase_ladder₀" => erase_ladder I X T hA hB hC P U hU hm

local notation "ladderBelow₀" => ladderBelow I X T hA hB hC P U hU hm

/-- The inherited row of a padded copy at a padded copy is the actual ladder row. -/
theorem row_ladder c v :
    Semantics.E Rows (ladderAt₀ c).1
      (ladderBelow₀ c v) = SupportLadderRows.row ranks₁ c v := by
  have hv : GradedLe (CellScheme.cell Base (addedB v)) (CellScheme.cell Base (addedB c)) := by
    rw [base_added_cell, base_added_cell]; exact GradedLe.refl _
  have h1 : Semantics.E Rows (ladderAt₀ c).1
      (ladderBelow₀ c v) =
      P.rows.E (P.baseMap (addedB c)) ⟨P.baseMap (addedB v),
        by simpa only [P.base_index] using hv⟩ :=
    P.rows.E_congr (erase_ladder₀ c)
      (erase_ladder₀ v)
  rw [h1, P.base_row (addedB c) ⟨addedB v, hv⟩]
  have h2 : ladderRow₁ c (addedB v) = SupportLadderRows.row ranks₁ c v := by
    change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ c)
      (RelativeLadderLayer.rankIndex I.boundary (GrowthLeafRecognition.card_pos hA)
        (GrowthOrderedBase.field I) (fields X 1) (SupportLadderRows.parent c) (addedB v)) = _
    rw [RelativeLadderLayer.rankIndex_added]
    rfl
  exact (RelativeLadderLayer.row_added I.boundary I.rows (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper hB hC) c
    ⟨addedB v, hv⟩).trans h2

/-- The inherited row of a padded copy at a present original is the rank-coded source. -/
theorem row_ladder_original v (z : CellScheme.below Carrier (U, 1)) d
    (hz : eraseP z.1 = P.baseMap (oldB d)) :
    Semantics.E Rows (ladderAt₀ v).1
      ⟨z.1, by rw [ladder_index]; exact z.2⟩ =
      SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
        (ranks₁ (SupportLadderRows.parent v) (GrowthOrderedBase.field I d)) := by
  have hgd : I.boundary.grade d ≤ 1 := by
    have he := erase_grade P.carrier B C z.1
    change P.carrier.grade (eraseP z.1) = CellScheme.grade Carrier z.1 at he
    rw [hz] at he
    have h1 := congrArg Prod.snd (carrier_old_cell I X T hA hB hC P d)
    change P.carrier.grade (P.baseMap (oldB d)) = I.boundary.grade d at h1
    have h2 : CellScheme.grade Carrier z.1 ≤ 1 := z.2.2
    omega
  have hd : GradedLe (CellScheme.cell Base (oldB d)) (CellScheme.cell Base (addedB v)) := by
    rw [base_old_cell, base_added_cell]
    exact ⟨I.boundary.scope_subset d, hgd⟩
  have h1 : Semantics.E Rows (ladderAt₀ v).1
      ⟨z.1, by rw [ladder_index]; exact z.2⟩ =
      P.rows.E (P.baseMap (addedB v)) ⟨P.baseMap (oldB d),
        by simpa only [P.base_index] using hd⟩ :=
    P.rows.E_congr (erase_ladder₀ v) hz
  rw [h1, P.base_row (addedB v) ⟨oldB d, hd⟩]
  have h2 : ladderRow₁ v (oldB d) = SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
      (ranks₁ (SupportLadderRows.parent v) (GrowthOrderedBase.field I d)) := by
    change SupportLadderRows.source (SupportLadderRows.ceiling ranks₁ v)
      (RelativeLadderLayer.rankIndex I.boundary (GrowthLeafRecognition.card_pos hA)
        (GrowthOrderedBase.field I) (fields X 1) (SupportLadderRows.parent v) (oldB d)) = _
    rw [RelativeLadderLayer.rankIndex_old]
  exact (RelativeLadderLayer.row_added I.boundary I.rows (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.field I) (fields X 1) (GrowthOrderedBase.proper hB hC) v
    ⟨oldB d, hd⟩).trans h2

/-! ## Recognition at grade one -/

variable {p : CellScheme.below (GrowthReplicatedRows.carrier P) (U, 1) → ExtOrd}

local notation "ladder_index₀" => ladder_index I X T hA hB hC P U hU hm

variable {I X T hA hB hC P U} in
theorem ladder_lawful (hp : RespectsSemanticsBelow Rows (U, 1) p) :
    Lawful ranks₁ (fun v => p (ladderAt₀ v)) := by
  constructor
  · intro v
    have hv := hp.orderly (ladderAt₀ v)
    change p _ = extVisibilityReplace (p _) (CellScheme.cell Carrier _).2
      (CellScheme.cell Carrier _).2 at hv
    rw [ladder_index] at hv
    exact hv.symm
  · intro c
    have ht := (hp.locality (ladderAt₀ c)).reindex
      (ladderBelow₀ c)
    exact transformsTo_congr
      (funext fun v => congrArg Prod.snd (ladder_index₀ v))
      (funext (row_ladder I X T hA hB hC P U hU hm c)) rfl ht

variable (p)

/-- The maximum of `p` over the copies at `U` of the shadows of a field. -/
def shadowSup f :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt₀ (shadow b f))

variable {I X T hA hB hC P U} in
/-- The maximum of `p` over the copies at `U` of the spare rungs. -/
def spareSup :=
  (Finset.univ : Finset (Catalogue X 1)).sup fun b =>
    p (ladderAt₀ (spare b))

variable {p}

local notation "spareSup₀" => spareSup hU hm p

theorem ladder_le_spareSup (hp : RespectsSemanticsBelow Rows (U, 1) p) v :
    p (ladderAt₀ v) ≤ spareSup₀ :=
  ((ladder_lawful hU hm hp).le_parent
    (GrowthLeafRecognition.rank_le_rungs I X) (GrowthLeafRecognition.rungs_pos I) v).trans
    (Finset.le_sup (f := fun b => p (ladderAt₀ (spare b)))
      (Finset.mem_univ _))

local notation "ladder_le_spareSup₀" => ladder_le_spareSup I X T hA hB hC P U hU hm

local notation "zeroMember₀" => GrowthLeafRecognition.zeroMember I X 1 le_rfl

/-- Availability bounds every grade-one value at `U` by the spare maximum. -/
theorem grade_one_le (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (z : CellScheme.below Carrier (U, 1)) (hz : CellScheme.grade Carrier z.1 = 1) :
    p z ≤ spareSup₀ := by
  let a₀ := zeroMember₀
  obtain ⟨w, hw, hzw⟩ := hp.availability z (ladderAt₀ (spare a₀))
    (by change CellScheme.scope Carrier z.1 ⊆ (CellScheme.cell Carrier _).1
        rw [ladder_index]; exact z.2.1)
    (hz.trans (congrArg Prod.snd (ladder_index₀ _)).symm)
  have hw' := hw.trans (ladder_index₀ _)
  have hei := ScopeReplicationCharts.erase_index P.carrier B C coverP hm w.1 hw'
  obtain ⟨v, hv⟩ := eq_added_of_full_one I X T hA hB hC P _ hei
  have he  :=
    GrowthReplicatedRows.copy_eq P hp
      (by change (CellScheme.cell Carrier w.1).1 ⊆ (CellScheme.cell Carrier _).1
          rw [hw', ladder_index])
      (hv.trans (erase_ladder₀ v).symm)
  exact hzw.trans (he.trans_le (ladder_le_spareSup₀ hp v))

/-- **The maximal spare chart at `U`**: it reads every padded copy exactly and every present
original as the rank-coded source of its field. -/
theorem exists_spare_chart (hp : RespectsSemanticsBelow Rows (U, 1) p) :
    ∃ a τ, Witness (gTop 1) τ ∧
      p (ladderAt₀ (spare a)) = spareSup₀ ∧
      (BoundedBy τ spareSup₀) ∧
      (∀ v , τ (SupportLadderRows.row ranks₁ (spare a) v) =
        p (ladderAt₀ v)) ∧
      ∀ z d,
        eraseP z.1 = P.baseMap (oldB d) →
        τ (SupportLadderRows.source rungs (ranks₁ a (GrowthOrderedBase.field I d))) = p z := by
  obtain ⟨a, -, hmax⟩ := Finset.exists_max_image (Finset.univ)
    (fun b => p (ladderAt₀ (spare b)))
    ⟨zeroMember₀, Finset.mem_univ _⟩
  let c := ladderAt₀ (spare a)
  have hpc : p c = spareSup₀ :=
    le_antisymm (Finset.le_sup (f := fun b => p (ladderAt₀ (spare b)))
      (Finset.mem_univ a)) (Finset.sup_le hmax)
  let self : CellScheme.below Carrier (CellScheme.cell Carrier c.1) := ⟨c.1, GradedLe.refl _⟩
  obtain ⟨τ, hτ, hb, hr⟩ := exists_bounded_exact_capped_witness
    (c := self) (fun d => d.2.2) (hp.orderly c).symm (hp.locality c)
  have hgrade : CellScheme.grade Carrier c.1 = 1 :=
    congrArg Prod.snd (ladder_index₀ _)
  refine ⟨a, τ, hgrade ▸ hτ, hpc, fun x => (hb x).trans_eq hpc, ?_, ?_⟩
  · intro v
    have h := hr (ladderBelow₀ (spare a) v)
    rw [row_ladder] at h
    exact h.trans (min_eq_left
      ((ladder_le_spareSup₀ hp v).trans_eq hpc.symm))
  · intro z d hz
    have hg : CellScheme.grade Carrier z.1 = 1 := by
      have h1 : CellScheme.grade Carrier z.1 ≤ 1 := z.2.2
      have h2 := CellScheme.grade_pos Carrier z.1
      omega
    let e : CellScheme.below Carrier (CellScheme.cell Carrier c.1) :=
      ⟨z.1, by rw [ladder_index]; exact z.2⟩
    have h := hr e
    rw [row_ladder_original I X T hA hB hC P U hU hm (spare a) z d hz,
      SupportLadderRows.ceiling_leaf] at h
    exact h.trans (min_eq_left
      ((grade_one_le I X T hA hB hC P U hU hm hp z hg).trans_eq hpc.symm))

section

variable {a : Catalogue X 1} {τ : LabelMap} (hτ : Witness (gTop 1) τ)
  (hread : ∀ v ,
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))

include hτ hread

/-- **Uncapped complete-field recognition at `U`**, on every field. -/
theorem shadowSup_eq_spare f :
    shadowSup I X T hA hB hC P U hU hm p f =
      τ (SupportLadderRows.source rungs (ranks₁ a f)) := by
  have he := SupportLadderRows.readout_image 
    (GrowthLeafRecognition.rank_le_rungs I X) a (SupportLadderRows.source_mono rungs) f
  simp  [SupportLadderRows.readout] at he
  
  rw [← he, Finset.apply_sup_eq_sup_comp_of_linearOrder τ hτ.mono hτ.bot, shadowSup]
  congr 1
  funext b
  rw [ ← hread, ]
  rfl

variable {I X T hA hB hC P U hU hm} in
/-- **Finite bottom reflection** on every ladder value of the maximal spare, when `M₁ p ≠ ⊥`. -/
def spare_bottom_reflection (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (hmax : p (ladderAt₀ (spare a)) =
      spareSup₀)
    (hne : spareSup₀ ≠ ⊥) v := by
  have : Nonempty (Catalogue X 1) := ⟨zeroMember₀⟩
  have hread' (w : Pt) : τ (SupportLadderRows.row ranks₁ (spare a) w) =
      min (p (ladderAt₀ w)) (spareSup₀) := by
    rw [hread, min_eq_left (ladder_le_spareSup₀ hp w)]
  have hdiag  := (hread _).trans hmax
  exact SupportLadderRows.bottom_reflection (GrowthLeafRecognition.rank_le_rungs I X)
    (GrowthLeafRecognition.rungs_pos I) (ladder_lawful hU hm hp)
    (spare a) hτ.bot hne hread' hdiag v

end

/-- **Exact readback of present originals at `U`**: uncapped. -/
theorem original_readback_one (hp : RespectsSemanticsBelow Rows (U, 1) p)
    (z : CellScheme.below Carrier (U, 1)) d
    (hz : eraseP z.1 = P.baseMap (oldB d)) :
    p z = shadowSup I X T hA hB hC P U hU hm p (GrowthOrderedBase.field I d) := by grind [exists_spare_chart, shadowSup_eq_spare]

/-! ## The lawful extension to the full scope -/

section

variable {a : Catalogue X 1} {τ : LabelMap} (hτ : Witness (gTop 1) τ)
  (hp : RespectsSemanticsBelow (GrowthReplicatedRows.rows P) (U, 1) p)
  (hmax : p (ladderAt I X T hA hB hC P U hU hm (SupportLadderRows.leaf
    (GrowthLeafRecognition.rungs_pos I) a)) = spareSup hU hm p)
  (hb : BoundedBy τ (spareSup hU hm p))
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))

include hτ hp hmax hb hread

/-- The chart transports the spare's whole ladder row on the padded base. -/
theorem base_section_lawful :
    RespectsSemanticsBelow BaseRows (A, 1) (fun d => τ (ladderRow₁ (spare a) d.1)) := by
  have hlad := RelativeLadderLayer.ladder_respects
    (GrowthLeafRecognition.card_pos hA)
    (GrowthOrderedBase.proper hB hC) (GrowthOrderedBase.anchor_lawful I X T) (spare a)
  by_cases hne : spareSup₀ = ⊥
  · have hz : ∀ x, τ x = ⊥ := fun x => le_bot_iff.mp ((hb x).trans_eq hne)
    simp  [hz]
    exact (RespectsSemanticsBelow.bot _ _)
  · refine map_respects_of_bottom_reflection hlad (fun d => d.2.2) (boundedMap_of_witness hτ)
      fun d => ?_
    rcases RelativeLadderLayer.cell_cases d.1 with
      ⟨e, he⟩ | ⟨v, hv⟩
    · rw [he, GrowthSpareRecognition.ladderRow_spare_old I X hA a e,
        ← GrowthLeafRecognition.index_shadow_self I X a, ]
      exact spare_bottom_reflection hτ hread hp hmax hne _
    · rw [hv, GrowthSpareRecognition.ladderRow_spare_added I X hA a v]
      exact spare_bottom_reflection hτ hread hp hmax hne v

end

/-- The extension's values on the installed layer: the chart's reading of the spare's row at
base cells, `⊥` elsewhere (no other cell lies below grade one). -/
def layerSection (a : Catalogue X 1) (τ : LabelMap) (c : Cell P.carrier) :=  if h : ∃ b, c = P.baseMap b then τ (ladderRow₁ (spare a) h.choose) else ⊥

local notation "layerSection₀" => layerSection I X T hA hB hC P

theorem layerSection_baseMap (a : Catalogue X 1) (τ : LabelMap) (b : Cell Base) :
    layerSection₀ a τ (P.baseMap b) = τ (ladderRow₁ (spare a) b) := by
  classical
  unfold layerSection
  split_ifs with h
  · exact congrArg (fun x => τ (ladderRow₁ (spare a) x)) (P.base_mono.injective h.choose_spec.symm)
  · exact absurd ⟨b, rfl⟩ h

section

variable {a : Catalogue X 1} {τ : LabelMap} (hτ : Witness (gTop 1) τ)
  (hp : RespectsSemanticsBelow (GrowthReplicatedRows.rows P) (U, 1) p)
  (hmax : p (ladderAt I X T hA hB hC P U hU hm (SupportLadderRows.leaf
    (GrowthLeafRecognition.rungs_pos I) a)) = spareSup hU hm p)
  (hb : BoundedBy τ (spareSup hU hm p))
  (hread : ∀ v : RelativeLadderLayer.Point (X := Field I.right.scheme I.left.scheme)
      (Q := Catalogue X 1),
    τ (SupportLadderRows.row (RelativeLadderLayer.ranks (fields X 1))
      (SupportLadderRows.leaf (GrowthLeafRecognition.rungs_pos I) a) v) =
        p (ladderAt I X T hA hB hC P U hU hm v))

include hτ hp hmax hb hread

/-- The layer section is lawful through grade one on the installed layer. -/
theorem layerSection_lawful :
    RespectsSemanticsBelow P.rows (A, 1) (fun d => layerSection₀ a τ d.1) := by
  have hbase := base_section_lawful I X T hA hB hC P U hU hm hτ hp hmax hb hread
  have h := P.base_respects (addedB (spare a)) (layerSection₀ a τ)
  have hrhs : RespectsSemanticsBelow BaseRows (CellScheme.cell Base (addedB (spare a)))
      (fun d => layerSection₀ a τ (P.baseMap d.1)) := by
    have hc := GradeCutLayerRows.cast_respects
      (base_added_cell I X T hA hB hC (spare a)).symm hbase
    have he : (fun d : CellScheme.below Base (CellScheme.cell Base (addedB (spare a))) =>
        τ (ladderRow₁ (spare a) d.1)) =
        fun d => layerSection₀ a τ (P.baseMap d.1) :=
      funext fun d => (layerSection_baseMap I X T hA hB hC P a τ d.1).symm
    rw [← he]
    exact hc
  have hlhs := h.mpr hrhs
  have hc := GradeCutLayerRows.cast_respects
    (carrier_added_cell I X T hA hB hC P (spare a)) hlhs
  exact hc

end

/-! ## The extension on the replicated carrier -/

def A_mem_plan := by
  have h := P.carrier.scope_mem_plan
    (P.baseMap (addedB (spare (zeroMember₀))))
  rwa [scope_added] at h


/-! ## Uniqueness -/

/-! ## The grade-one mixed capped lift -/

