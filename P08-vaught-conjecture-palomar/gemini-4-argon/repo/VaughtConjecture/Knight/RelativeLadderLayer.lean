/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.ReceivingCatalogueIncidences

/-! # The first relative mixed layer

Append actual grade-one rungs and shadows to a proper inherited boundary.
The inputs are scalar sections lawful on that boundary, not lawful physical
predecessor vectors. Rank postprocessing constructs their incidences with all
inherited grade-one owners, including long rows. Every shadow, including a
zero-rank shadow, has a separately installed same-source ceiling leaf.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd LadderScalarRendering

variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → X) (fields : Q → X → ExtOrd)

def ranks (a : Q) (x : X) : ℕ := fieldRank (fields a) x
def rungs : ℕ := Fintype.card X + 1

local notation "rungs'" => rungs (X := X)

abbrev Point := SupportLadderRows.Point rungs' X Q

local notation "Pt" => Point (X := X) (Q := Q)

abbrev carrier := SourceLayerCarrier.scheme D Pt 1 Nat.one_pos hA

local notation "Car" => carrier D hA (X := X) (Q := Q)
local notation "Cbelow" => CellScheme.below (carrier D hA (X := X) (Q := Q))
local notation "Ccell" => CellScheme.cell (carrier D hA (X := X) (Q := Q))
local notation "Cgrade" => CellScheme.grade (carrier D hA (X := X) (Q := Q))

abbrev old (d : Cell D) : Cell Car := SourceLayerCarrier.toCell D Pt 1 Nat.one_pos hA (.inl d)
abbrev added (v : Pt) : Cell Car := SourceLayerCarrier.toCell D Pt 1 Nat.one_pos hA (.inr v)
abbrev view := SourceLayerCarrier.toOcc D Pt 1 Nat.one_pos hA

local notation "old'" => old D hA
local notation "added'" => added D hA
local notation "view'" => view D hA

theorem old_index (d : Cell D) : Ccell (old' d) = D.cell d :=
  SourceLayerCarrier.cell_toCell D _ 1 Nat.one_pos hA (.inl d)
theorem added_index (v : Pt) : Ccell (added' v) = (A, 1) :=
  SourceLayerCarrier.cell_toCell D _ 1 Nat.one_pos hA (.inr v)

theorem cell_cases (d : Cell Car) : (∃ c, d = old' c) ∨ ∃ v, d = added' v := by
  have h := (SourceLayerCarrier.toCell_toOcc D Pt 1 Nat.one_pos hA d).symm
  cases he : view' d with
  | inl c => exact Or.inl ⟨c, h.trans (congrArg _ he)⟩
  | inr v => exact Or.inr ⟨v, h.trans (congrArg _ he)⟩

def rankIndex (a : Q) (d : Cell Car) : ℕ :=
  match view' d with
  | .inl c => ranks fields a (field c)
  | .inr v => SupportLadderRows.index (ranks fields) a v

local notation "rkIdx" => rankIndex D hA field fields

@[simp] theorem rankIndex_old (a : Q) (d : Cell D) :
    rkIdx a (old' d) = ranks fields a (field d) := by
  simp only [rankIndex, old, view, SourceLayerCarrier.toOcc_toCell]
@[simp] theorem rankIndex_added (a : Q) (v : Pt) :
    rkIdx a (added' v) = SupportLadderRows.index (ranks fields) a v := by
  simp only [rankIndex, added, view, SourceLayerCarrier.toOcc_toCell]

omit [Fintype Q] in
theorem rank_bound (a : Q) (x : X) : ranks fields a x < rungs' :=
  Nat.lt_succ_of_le (fieldRank_le _ _)

theorem rankIndex_bound (a : Q) (d : Cell Car) : rkIdx a d ≤ rungs' := by
  unfold rankIndex
  split
  · exact (rank_bound fields _ _).le
  · exact SupportLadderRows.index_le _ _

theorem rankIndex_agreement (a b : Q) (d : Cell Car) :
    min (rkIdx a d) (FiniteProfileControllers.cut rungs' (ranks fields a) (ranks fields b)) =
      min (rkIdx b d) (FiniteProfileControllers.cut rungs' (ranks fields a) (ranks fields b)) := by
  unfold rankIndex
  split
  · exact FiniteProfileControllers.agree_cut _ _ _ _
  · exact SupportLadderRows.index_agreement _ _ _

def image (a : Q) (f : ℕ → ExtOrd) (d : Cell Car) : ExtOrd := f (rkIdx a d)

local notation "img" => image D hA field fields

def ladderRow (v : Pt) : Cell Car → ExtOrd :=
  img (SupportLadderRows.parent v)
    (SupportLadderRows.source (SupportLadderRows.ceiling (ranks fields) v))

local notation "ladRow" => ladderRow D hA field fields

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev separated := SeparatedSourceLayerCarrier.separated_of_proper D 1 hp
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D Pt 1 Nat.one_pos hA (separated D hp)
abbrev base := SeparatedSourceLayerCarrier.base D Pt 1 Nat.one_pos hA (separated D hp) sem

local notation "oEquiv" => ownerEquiv D hA hp
local notation "base'" => base D sem hA hp

theorem below_grade_one (v : Pt) (d : Cbelow (Ccell (added' v))) : Cgrade d.1 = 1 :=
  le_antisymm (by simpa only [CellScheme.grade, added_index] using d.2.2) (CellScheme.grade_pos Car d.1)

def rows : Semantics Car where
  E c d := match view' c with
    | .inl _ => Semantics.E base' c d
    | .inr v => ladRow v d.1
  orderly c d := by
    dsimp only
    split
    · exact Semantics.orderly base' c d
    · rename_i v h
      have hc : c = added' v :=
        (SourceLayerCarrier.toCell_toOcc D Pt 1 Nat.one_pos hA c).symm.trans (congrArg _ h)
      have hg : Cgrade d.1 = 1 := below_grade_one D hA v ⟨d.1, hc ▸ d.2⟩
      change _ = extVisibilityReplace _ (Cgrade d.1) _
      rw [hg]
      exact (SupportLadderRows.source_visible _ _).symm

local notation "rows'" => rows D sem hA field fields hp
local notation "rowsE" => Semantics.E (rows D sem hA field fields hp)

theorem row_added (v : Pt) (d : Cbelow (Ccell (added' v))) :
    rowsE (added' v) d = ladRow v d.1 := by
  simp only [rows, view, added, SourceLayerCarrier.toOcc_toCell]

theorem row_old (c : Cell D) (d : Cbelow (Ccell (old' c))) :
    rowsE (old' c) d = Semantics.E base' (old' c) d := by
  simp only [rows, view, old, SourceLayerCarrier.toOcc_toCell]

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    rowsE (old' c) (oEquiv c d) = sem.E c d := by
  rw [row_old]
  exact SeparatedSourceLayerCarrier.base_old D _ 1 Nat.one_pos hA (separated D hp) sem c d

theorem old_respects_iff (c : Cell D) (p : Cbelow (Ccell (old' c)) → ExtOrd) :
    RespectsSemanticsBelow rows' _ p ↔ RespectsSemanticsBelow sem (D.cell c) (p ∘ oEquiv c) := by
  have he (d : Cbelow (Ccell (old' c))) : rowsE d.1 = Semantics.E base' d.1 := by
    obtain ⟨d, rfl⟩ := (oEquiv c).surjective d
    exact funext (row_old D sem hA field fields hp d.1)
  rw [← SeparatedSourceLayerCarrier.base_respects_iff D _ 1 Nat.one_pos hA (separated D hp) sem c p]
  constructor <;> intro h <;> refine ⟨h.orderly, fun d => ?_, h.availability⟩
  · simpa only [he d] using h.locality d
  · rw [he d]; exact h.locality d

omit [Fintype Q] in
/-- The original-lawful input, not a completed physical source, supplies all
rank-coded old incidences. Long rows are handled by finite bottom reflection. -/
theorem rank_respects (a : Q)
    (ha : RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1))) (t : ℕ) :
    RespectsSemanticsBelow sem (A, 1)
      (fun d => SupportLadderRows.source t (ranks fields a (field d.1))) := by
  have hg (d : D.below (A, 1)) : D.grade d.1 = 1 := le_antisymm d.2.2 (D.grade_pos d.1)
  refine ⟨fun d => by
    change _ = extVisibilityReplace _ (D.grade d.1) (D.grade d.1)
    rw [hg]; exact (SupportLadderRows.source_visible _ _).symm, fun c => ?_, fun c v hs hgr => ?_⟩
  · have hgc (d : D.below (D.cell c.1)) : D.grade d.1 = 1 :=
      le_antisymm (d.2.2.trans c.2.2) (D.grade_pos d.1)
    have hgrade : (fun d : D.below (D.cell c.1) => D.grade d.1) = (fun _ => 1) := funext hgc
    rw [hgrade]
    by_cases ht : t = 0
    · subst t
      have hz (i : ℕ) : SupportLadderRows.source 0 i = ⊥ :=
        (SupportLadderRows.source_bot_iff _ _).mpr (Nat.min_zero i)
      simp only [hz, min_self]
      exact TransformsTo.to_bot _
    let f : ExtOrd → ExtOrd := fun x => SupportLadderRows.source t (rank (values (fields a)) x)
    have hm : Monotone f := (SupportLadderRows.source_mono t).comp (rank_mono _)
    have h0 : f ⊥ = ⊥ := by
      simp only [f, rank_bot (bot_not_values _), SupportLadderRows.source_zero]
    have hz (x : X) : f (fields a x) = ⊥ ↔ fields a x = ⊥ := by
      change SupportLadderRows.source t (ranks fields a x) = ⊥ ↔ _
      rw [SupportLadderRows.source_bot_iff, Nat.min_eq_zero_iff, or_iff_left ht]
      refine ⟨fun hz => by_contra fun hn => ?_, fun hz => ?_⟩
      · have hh : 0 < ranks fields a x := rank_pos (mem_values.mpr ⟨hn, x, rfl⟩)
        omega
      · change rank (values (fields a)) (fields a x) = 0
        rw [hz]; exact rank_bot (bot_not_values _)
    have hl := ha.locality c
    rw [hgrade] at hl
    simpa only [hm.map_min, f, ranks, fieldRank] using
      ReceivingCatalogueIncidences.postprocess hl
        (fun d => by simpa only [hgc d] using (sem.orderly c.1 d).symm) hm h0
        (fun _ => SupportLadderRows.source_visible _ _)
        (fun d => by rw [hm.map_min, min_eq_bot, hz, hz, min_eq_bot])
  · obtain ⟨w, hw, hcw⟩ := ha.availability c v hs hgr
    exact ⟨w, hw, SupportLadderRows.source_mono t (rank_mono _ hcw)⟩

theorem image_respects {j : ℕ} (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hpos : ∀ i, 0 < i → i ≤ rungs' → f i ≠ ⊥)
    (hold : RespectsSemanticsBelow sem (A, j) (fun d => f (ranks fields a (field d.1)))) :
    RespectsSemanticsBelow rows' (A, j) (fun d => img a f d.1) := by
  refine ⟨fun d => ?_, fun c => ?_, fun c t hs hgr => ?_⟩
  · rcases cell_cases D hA d.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · simpa only [hx, CellScheme.grade, old_index, image, rankIndex_old] using
        hold.orderly ⟨x, by simpa only [hx, old_index] using d.2⟩
    · change _ = extVisibilityReplace _ (Cgrade d.1) _
      simp only [hv', CellScheme.grade, added_index]
      exact (hv _).symm
  · rcases cell_cases D hA c.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hl := RespectsSemanticsBelow.mono (by simpa only [hx, old_index] using c.2) hold
      have hphysical : RespectsSemanticsBelow rows' (Ccell (old' x)) (fun d => img a f d.1) := by
        apply (old_respects_iff D sem hA field fields hp x _).mpr
        simpa only [Function.comp_def, ownerEquiv,
          SeparatedSourceLayerCarrier.ownerEquiv_val, image, rankIndex_old,
          CellScheme.below.mono] using hl
      rcases c with ⟨c, hc⟩
      dsimp only at hx; subst c
      exact hphysical.locality ⟨old' x, GradedLe.refl _⟩
    · rcases c with ⟨c, hc⟩
      dsimp only at hv'; subst c
      let e := SupportLadderRows.index (ranks fields) a v
      have hec : e ≤ SupportLadderRows.ceiling (ranks fields) v := min_le_right _ _
      have hel : e ≤ rungs' := SupportLadderRows.index_le a v
      have he (d : Cell Car) :
          min (img a f d) (img a f (added' v)) =
            f (min (rkIdx (SupportLadderRows.parent v) d) e) := by
        simp only [image, rankIndex_added, ← hf.map_min]
        apply congrArg f
        have hag := rankIndex_agreement D hA field fields a (SupportLadderRows.parent v) d
        dsimp only [e, SupportLadderRows.index]
        grind
      refine transformsTo_congr (funext (below_grade_one D hA v)).symm
        (funext (row_added D sem hA field fields hp v)).symm (funext fun d => (he d.1).symm) ?_
      simp only [ladderRow, image]
      by_cases hz : e = 0
      · simp only [hz, Nat.min_zero, h0]; exact TransformsTo.to_bot _
      · simpa only [min_assoc, min_eq_right hec] using
          SupportLadderRows.transforms_positive
            (fun d : Cbelow (Ccell (added' v)) => rkIdx (SupportLadderRows.parent v) d.1)
            (SupportLadderRows.ceiling (ranks fields) v) (fun i => f (min i e))
            (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0) (fun _ => hv _)
            (fun i hi _ => hpos _ (by omega) ((min_le_right _ _).trans hel))
  · rcases cell_cases D hA t.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hct : GradedLe (Ccell c.1) (Ccell (old' x)) := hx ▸ ⟨hs, hgr.le⟩
      obtain ⟨y, hy⟩ := (oEquiv x).surjective ⟨c.1, hct⟩
      have hy' : c.1 = old' y.1 := (congrArg Subtype.val hy).symm
      have hx' : GradedLe (D.cell x) (A, j) := by simpa only [hx, old_index] using t.2
      obtain ⟨w, hw, hle⟩ := hold.availability ⟨y.1, y.2.trans hx'⟩ ⟨x, hx'⟩
        (by simpa only [hy', hx, CellScheme.scope, old_index] using hs)
        (by simpa only [hy', hx, CellScheme.grade, old_index] using hgr)
      refine ⟨⟨old' w.1, by rw [old_index]; exact w.2⟩, ?_, ?_⟩
      · rw [old_index, hx, old_index]; exact hw
      · simpa only [hy', image, rankIndex_old] using hle
    · let leaf : Pt := SupportLadderRows.leaf (Nat.succ_pos _) a
      refine ⟨⟨added' leaf, by simpa only [hv', added_index] using t.2⟩, ?_, ?_⟩
      · rw [added_index, hv', added_index]
      · apply hf
        have hl : rkIdx a (added' leaf) = rungs' :=
          (rankIndex_added D hA field fields a leaf).trans
            ((SupportLadderRows.index_leaf (profile := ranks fields) (Nat.succ_pos _) a a).trans
              (FiniteProfileControllers.cut_refl _ _))
        exact (rankIndex_bound D hA field fields a c.1).trans_eq hl.symm

/-- All new long rows are lawful on the installed lower domain, rather than
only on the abstract ladder table. -/
theorem ladder_respects
    (hinput : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1)))
    (v : Pt) : RespectsSemanticsBelow rows' (A, 1) (fun d => ladRow v d.1) := by
  by_cases ht : SupportLadderRows.ceiling (ranks fields) v = 0
  · have hz (d : Cell Car) : ladRow v d = ⊥ :=
      (SupportLadderRows.source_bot_iff _ _).mpr (by simp [ht])
    simp only [hz]
    exact respectsBelow_bot _ (A, 1)
  · exact image_respects D sem hA field fields hp (SupportLadderRows.parent v) _
      (SupportLadderRows.source_mono _) (SupportLadderRows.source_zero _)
      (SupportLadderRows.source_visible _)
      (fun i hi _ hz => by have := (SupportLadderRows.source_bot_iff _ _).mp hz; omega)
      (rank_respects D sem field fields _ (hinput _) _)

theorem consistent (hs : sem.IsConsistent)
    (hinput : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1))) :
    Semantics.IsConsistent rows' := by
  intro c
  rcases cell_cases D hA c with ⟨c, rfl⟩ | ⟨v, rfl⟩
  · apply (old_respects_iff D sem hA field fields hp c _).mpr
    simpa only [Function.comp_def, inherited_row] using hs c
  · have hr := GradeCutLayerRows.cast_respects Car rows' (added_index D hA v).symm
      (ladder_respects D sem hA field fields hp hinput v)
    convert hr using 1
    exact funext (row_added D sem hA field fields hp v)

theorem coded (hs : sem.IsCoded) : Semantics.IsCoded rows' := by
  intro c d
  rcases cell_cases D hA c with ⟨c, rfl⟩ | ⟨v, rfl⟩
  · obtain ⟨d, rfl⟩ := (oEquiv c).surjective d
    rw [inherited_row]
    simpa only [CellScheme.grade, old_index] using hs c d
  · rw [row_added]
    simpa only [CellScheme.grade, added_index, ladderRow, image] using
      SupportLadderRows.source_coded (SupportLadderRows.ceiling (ranks fields) v)
        (rkIdx (SupportLadderRows.parent v) d.1)

