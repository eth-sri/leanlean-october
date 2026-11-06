
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
import VaughtConjecture.Knight.ReceivingCatalogueIncidences

/-! # The first relative mixed layer

Append actual grade-one rungs and shadows to a proper inherited boundary.
The inputs are scalar sections lawful on that boundary, not lawful physical
predecessor vectors. Rank postprocessing constructs their incidences with all
inherited grade-one owners, including long rows. Every shadow, including a
zero-rank shadow, has a separately installed same-source ceiling leaf.
-/

namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value  LadderScalarRendering
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
variable (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
variable (field : Cell D → X) (fields : Q → X → ExtOrd)

def ranks a x := fieldRank (fields a) x
def rungs := Fintype.card X + 1
local notation "rungs₀" => rungs (X := X)

abbrev Point := SupportLadderRows.Point (rungs₀) X Q
local notation "Point₀" => Point (X := X) (Q := Q)

abbrev carrier := SourceLayerCarrier.scheme D (Point₀) 1 Nat.one_pos hA
local notation "carrier₀" => carrier D hA (X := X) (Q := Q)

abbrev old (d : Cell D) : Cell (carrier₀) :=
  SourceLayerCarrier.toCell D (Point  ) 1 Nat.one_pos hA (.inl d)
abbrev added (v : Point₀) : Cell (carrier₀) :=
  SourceLayerCarrier.toCell D (Point  ) 1 Nat.one_pos hA (.inr v)
abbrev view := SourceLayerCarrier.toOcc D (Point₀) 1 Nat.one_pos hA

local notation "old₀" => old D hA

variable {D hA} in
theorem old_index d : (carrier₀).cell (old₀ d) = D.cell d :=
  SourceLayerCarrier.cell_toCell D _ 1 Nat.one_pos hA (.inl d)
local notation "added₀" => added D hA

theorem added_index (v : Point₀) :
    (carrier₀).cell (added₀ v) = (A, 1) :=
  SourceLayerCarrier.cell_toCell D _ 1 Nat.one_pos hA (.inr v)

variable {D hA} in
theorem cell_cases (d : Cell (carrier₀)) :
    (∃ c, d = old₀ c) ∨ ∃ v, d = added₀ v := by
  cases he : view D hA d with
  | inl c =>
      grind [SourceLayerCarrier.toCell_toOcc]
  | inr v =>
      grind [SourceLayerCarrier.toCell_toOcc]

local notation "ranks₀" => ranks fields

def rankIndex a (d : Cell (carrier₀)) :=
  match view D hA d with
  | .inl c => ranks₀ a (field c)
  | .inr v => SupportLadderRows.index (ranks₀) a v

local notation "rankIndex₀" => rankIndex D hA field fields

variable {D hA field fields} in
@[simp] theorem rankIndex_old a d :
    rankIndex₀ a (old₀ d) = ranks₀ a (field d) := by
  simp  [rankIndex,   ]
@[simp] theorem rankIndex_added a (v : Point₀) :
    rankIndex₀ a (added₀ v) = SupportLadderRows.index (ranks₀) a v := by
  simp  [rankIndex,   ]

omit [Fintype Q] in
theorem rank_bound a x : ranks₀ a x < rungs₀ :=
  Nat.lt_succ_of_le (fieldRank_le _ _)

omit [Fintype Q] in
theorem rank_zero a x : ranks₀ a x = 0 ↔ fields a x = ⊥ := by
  constructor
  · intro hz
    by_contra hn
    have hh := rank_pos (mem_values.mpr ⟨hn, x, rfl⟩)
    change 0 < ranks₀ a x at hh
    omega
  · intro hz
    change rank (values (fields a)) (fields a x) = 0
    rw [hz]
    exact rank_bot (bot_not_values)

variable {D hA field fields} in
theorem rankIndex_bound a (d : Cell (carrier₀)) :
    rankIndex₀ a d ≤ rungs₀ := by
  unfold rankIndex
  split
  · exact (rank_bound fields _ _).le
  · exact SupportLadderRows.index_le _ _

theorem rankIndex_agreement a b (d : Cell (carrier₀)) :
    min (rankIndex₀ a d)
        (FiniteProfileControllers.cut (rungs₀) (ranks₀ a) (ranks₀ b)) =
      min (rankIndex₀ b d)
        (FiniteProfileControllers.cut (rungs₀) (ranks₀ a) (ranks₀ b)) := by
  unfold rankIndex
  split
  · exact FiniteProfileControllers.agree_cut _ _ _ _
  · exact SupportLadderRows.index_agreement _ _ _

def image (a : Q) (f : ℕ → ExtOrd) (d : Cell (carrier₀)) :=
  f (rankIndex₀ a d)

local notation "ceiling₀" => SupportLadderRows.ceiling (ranks fields)

local notation "image₀" => image D hA field fields

def ladderRow (v : Point₀) :=
  image₀ (SupportLadderRows.parent v)
    (SupportLadderRows.source (ceiling₀ v))

variable (hp : AvoidsValue D.scope A)

abbrev separated := SeparatedSourceLayerCarrier.separated_of_proper D 1 hp
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D
  (Point₀) 1 Nat.one_pos hA (separated D hp)
abbrev base := SeparatedSourceLayerCarrier.base D
  (Point₀) 1 Nat.one_pos hA (separated D hp) sem

theorem below_grade_one (v : Point₀)
    (d : (carrier₀).below
      ((carrier₀).cell (added₀ v))) :
    (carrier₀).grade d.1 = 1 :=
  le_antisymm (by simpa only [CellScheme.grade, added_index] using d.2.2)
    ((carrier₀).grade_pos d.1)

local notation "base₀" => base D sem hA hp

local notation "ladderRow₀" => ladderRow D hA field fields

def rows : Semantics (carrier₀) where
  E c d := match view D hA c with
    | .inl _ => (base₀).E c d
    | .inr v => ladderRow₀ v d.1
  orderly c d := by
    dsimp only
    split
    · exact (base₀).orderly c d
    · rename_i v h
      have hc : c = added₀ v := by
        rw [← SourceLayerCarrier.toCell_toOcc c]
        exact congrArg (SourceLayerCarrier.toCell D _ 1 Nat.one_pos hA) h
      have hg  :=
        below_grade_one D hA v ⟨d.1, hc ▸ d.2⟩
      change _ = extVisibilityReplace _
        ((carrier₀).grade d.1) _
      rw [hg]
      exact (SupportLadderRows.source_visible _ _).symm

local notation "rows₀" => rows D sem hA field fields hp

theorem row_added (v : Point₀)
    (d : (carrier₀).below
      ((carrier₀).cell (added₀ v))) :
    (rows₀).E (added₀ v) d = ladderRow₀ v d.1 := by
  simp  [rows,   ]

theorem row_old (c : Cell D)
    (d : (carrier₀).below
      ((carrier₀).cell (old₀ c))) :
    (rows₀).E (old₀ c) d = (base₀).E (old₀ c) d := by
  simp  [rows,   ]

local notation "ownerEquiv₀" => ownerEquiv D hA hp

theorem inherited_row (c : Cell D) (d : D.belowCell c) :
    (rows₀).E (old₀ c) (ownerEquiv₀ c d) = sem.E c d := by
  rw [row_old]
  exact SeparatedSourceLayerCarrier.base_old D _ 1 Nat.one_pos hA (separated D hp) sem d

variable {D sem hA field fields hp} in
theorem old_respects_iff (c : Cell D)
    (p : (carrier₀).below
      ((carrier₀).cell (old₀ c)) → ExtOrd) :
    RespectsSemanticsBelow (rows₀) _ p ↔
      Semantics.RowLawful sem c (p ∘ ownerEquiv₀ c) := by
  have he (d : (carrier₀).below
      ((carrier₀).cell (old₀ c))) :
      (rows₀).E d.1 = (base₀).E d.1 := by
    obtain ⟨d, rfl⟩ := (ownerEquiv₀ c).surjective d
    exact funext (row_old D sem hA field fields hp d.1)
  rw [← SeparatedSourceLayerCarrier.base_respects_iff
    (separated D hp) sem c p]
  constructor <;> intro h <;> refine ⟨h.orderly, ?_, h.availability⟩
  · intro d
    simpa only [he d] using h.locality d
  · intro d
    rw [he d]
    exact h.locality d

local notation "RespectsSemanticsBelow₀" => RespectsSemanticsBelow sem (A, 1)

omit [Fintype Q] in
/-- The original-lawful input, not a completed physical source, supplies all
rank-coded old incidences. Long rows are handled by finite bottom reflection. -/
theorem rank_respects a
    (ha : RespectsSemanticsBelow₀ (fun d => fields a (field d.1))) t :
    RespectsSemanticsBelow₀
      (fun d => SupportLadderRows.source t (ranks₀ a (field d.1))) := by
  have hg (d : D.below (A, 1)) : D.grade d.1 = 1 := le_antisymm d.2.2 (D.grade_pos d.1)
  refine ⟨fun d => by
    grind [SupportLadderRows.source_visible], ?_, ?_⟩
  · intro c
    have hgc (d : D.belowCell c.1) : D.grade d.1 = 1 :=
      le_antisymm (d.2.2.trans c.2.2) (D.grade_pos d.1)
    have hgrade  := funext hgc
    rw [hgrade]
    by_cases ht : t = 0
    · subst t
      have hz (i : ℕ) : SupportLadderRows.source 0 i = ⊥ :=
        (SupportLadderRows.source_bot_iff _ _).mpr (Nat.min_zero i)
      simp only [hz, min_self]
      exact TransformsTo.to_bot
    let f  := fun x => SupportLadderRows.source t (rank (values (fields a)) x)
    have hm : Monotone f := (SupportLadderRows.source_mono t).comp (rank_mono _)
    have h0 : f ⊥ = ⊥ := by
      simp only [f, rank_bot (bot_not_values), SupportLadderRows.source_zero]
    have hz (x : X) : f (fields a x) = ⊥ ↔ fields a x = ⊥ := by
      
      rw [SupportLadderRows.source_bot_iff, Nat.min_eq_zero_iff, or_iff_left ht]
      exact rank_zero fields a x
    have hl := ha.locality c
    rw [hgrade] at hl
    have hout := ReceivingCatalogueIncidences.postprocess hl
      (fun d => by simpa only [hgc d] using (sem.orderly c.1 d).symm) hm h0
      (fun _ => SupportLadderRows.source_visible _ _)
      (fun d => by grind)
    simpa only [hm.map_min, f, ranks, fieldRank] using hout
  · intro c v hs hgr
    obtain ⟨w, hw, hcw⟩ := ha.availability c v hs hgr
    exact ⟨w, hw, SupportLadderRows.source_mono t (rank_mono _ hcw)⟩

/-- Locality at every installed rung, on its complete actual domain. -/
theorem image_locality (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hpos : ∀ i, 0 < i → i ≤ rungs₀ → f i ≠ ⊥)
    (v : Point₀) :
    TransformsTo (fun d =>
      (carrier₀).grade d.1)
      ((rows₀).E (added₀ v))
      (fun d => min (image₀ a f d.1)
        (image₀ a f (added₀ v))) := by
  let e := SupportLadderRows.index (ranks₀) a v
  have hec : e ≤ ceiling₀ v := min_le_right _ _
  have hel : e ≤ rungs₀ := SupportLadderRows.index_le a v
  have he (d : Cell (carrier₀)) :
      min (image₀ a f d) (image₀ a f (added₀ v)) =
        f (min (rankIndex₀ (SupportLadderRows.parent v) d) e) := by
    simp  [image,  ← hf.map_min]
    apply congrArg f
    have hag := rankIndex_agreement D hA field fields a (SupportLadderRows.parent v) d
    dsimp  [e, SupportLadderRows.index]
    grind
  rw [show (fun d : (carrier₀).below
      ((carrier₀).cell (added₀ v)) =>
    (carrier₀).grade d.1) = (fun _ => 1) from funext (below_grade_one D hA v)]
  rw [funext (row_added D sem hA field fields hp v),
    show (fun d : (carrier₀).below
        ((carrier₀).cell (added₀ v)) =>
      min (image₀ a f d.1)
        (image₀ a f (added₀ v))) =
      (fun d => f (min (rankIndex₀ (SupportLadderRows.parent v) d.1) e))
      from funext (fun d => he d.1)]
  simp only [ladderRow, image]
  by_cases hz : e = 0
  · simp only [hz, Nat.min_zero, h0]
    exact TransformsTo.to_bot
  · have ht := SupportLadderRows.transforms_positive
      (fun d : (carrier₀).below
        ((carrier₀).cell (added₀ v)) =>
        rankIndex₀ (SupportLadderRows.parent v) d.1)
      (ceiling₀ v) (fun i => f (min i e))
      (fun _ _ h => hf (min_le_min_right _ h)) (by simpa using h0) (fun _ => hv _)
      (fun i hi _ => hpos _ (by omega) ((min_le_right _ _).trans hel))
    simpa only [min_assoc, min_eq_right hec] using ht

local notation "rows₀₀" => rows D sem hA field fields hp

theorem image_respects {j : ℕ} (a : Q) (f : ℕ → ExtOrd) (hf : Monotone f) (h0 : f 0 = ⊥)
    (hv : ∀ i, SelfVis 1 (f i)) (hpos : ∀ i, 0 < i → i ≤ rungs₀ → f i ≠ ⊥)
    (hold : RespectsSemanticsBelow sem (A, j) (fun d => f (ranks₀ a (field d.1)))) :
    RespectsSemanticsBelow (rows₀₀) (A, j)
      (fun d => image D hA field fields a f d.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    rcases cell_cases d.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hxd : GradedLe (D.cell x) (A, j) := by
        simpa only [hx, old_index] using d.2
      simpa only [hx, CellScheme.grade, old_index, image, rankIndex_old] using
        hold.orderly ⟨x, hxd⟩
    · change _ = extVisibilityReplace _ ((carrier D hA).grade d.1) _
      simp only [hv', CellScheme.grade, added_index]
      exact (hv _).symm
  · intro c
    rcases cell_cases c.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hxc : GradedLe (D.cell x) (A, j) := by
        simpa only [hx, old_index] using c.2
      have hl := RespectsSemanticsBelow.mono hxc hold
      have hphysical : RespectsSemanticsBelow (rows₀₀)
          ((carrier₀).cell (old₀ x))
          (fun d => image D hA field fields a f d.1) := by
        apply (old_respects_iff x _).mpr
        simpa only [Function.comp_def, 
          SeparatedSourceLayerCarrier.ownerEquiv_val, image, rankIndex_old,
          CellScheme.below.mono] using hl
      have hh := hphysical.locality ⟨old₀ x, GradedLe.refl _⟩
      rcases c with ⟨c, hc⟩
      dsimp  at hx
      subst c
      exact hh
    · rcases c with ⟨c, hc⟩
      dsimp  at hv'
      subst c
      exact image_locality D sem hA field fields hp a f hf h0 hv hpos v
  · intro c t hs hgr
    rcases cell_cases t.1 with ⟨x, hx⟩ | ⟨v, hv'⟩
    · have hct : GradedLe ((carrier₀).cell c.1)
          ((carrier₀).cell (old₀ x)) := hx ▸ ⟨hs, hgr.le⟩
      obtain ⟨y, hy⟩ := (ownerEquiv₀ x).surjective ⟨c.1, hct⟩
      have hy' : c.1 = old₀ y.1 := (congrArg Subtype.val hy).symm
      have hx' : GradedLe (D.cell x) (A, j) := by simpa only [hx, old_index] using t.2
      have hscope : D.scope y.1 ⊆ D.scope x := by
        simpa only [hy', hx, CellScheme.scope, old_index] using hs
      have hgrade : D.grade y.1 = D.grade x := by
        simpa only [hy', hx, CellScheme.grade, old_index] using hgr
      obtain ⟨w, hw, hle⟩ := hold.availability ⟨y.1, y.2.trans hx'⟩ ⟨x, hx'⟩ hscope hgrade
      refine ⟨⟨old₀ w.1, by rw [old_index]; exact w.2⟩, ?_, ?_⟩
      · rw [old_index, hx, old_index]; exact hw
      · simpa only [hy', image, rankIndex_old] using hle
    · let leaf : Point₀ := SupportLadderRows.leaf (Nat.succ_pos _) a
      refine ⟨⟨added₀ leaf, by simpa only [hv', added_index] using t.2⟩, ?_, ?_⟩
      · rw [added_index, hv', added_index]
      · change f _ ≤ f _
        apply hf
        have hl : rankIndex D hA field fields a (added₀ leaf) = rungs₀ :=  (rankIndex_added D hA field fields a leaf).trans
            ((SupportLadderRows.index_leaf (profile := ranks₀) (Nat.succ_pos _) a a).trans
              (FiniteProfileControllers.cut_refl _ _))
        exact (rankIndex_bound a c.1).trans_eq hl.symm

variable {D sem field fields} in
/-- All new long rows are lawful on the installed lower domain, rather than
only on the abstract ladder table. -/
theorem ladder_respects
    (hinput : ∀ a, RespectsSemanticsBelow₀ (fun d => fields a (field d.1)))
    (v : Point₀) :
    RespectsSemanticsBelow (rows₀) (A, 1)
      (fun d => ladderRow₀ v d.1) := by
  by_cases ht : ceiling₀ v = 0
  · have hz (d : Cell (carrier₀)) :
        ladderRow₀ v d = ⊥ :=  (SupportLadderRows.source_bot_iff _ _).mpr (by simp [ht])
    simp  [hz]
    exact ⟨fun _ => (selfVis_bot).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot,
      fun _ t _ _ => ⟨t, rfl, le_rfl⟩⟩
  · exact image_respects D sem hA field fields hp (SupportLadderRows.parent v) _
      (SupportLadderRows.source_mono _) (SupportLadderRows.source_zero _)
      (SupportLadderRows.source_visible _) (fun i hi _ hz => by
        grind [SupportLadderRows.source_bot_iff])
      (rank_respects D sem field fields _ (hinput _) _)

theorem consistent (hs : sem.IsConsistent)
    (hinput : ∀ a, RespectsSemanticsBelow₀ (fun d => fields a (field d.1))) :
    (rows₀₀).IsConsistent := by
  intro c
  rcases cell_cases c with ⟨c, rfl⟩ | ⟨v, rfl⟩
  · apply (old_respects_iff c _).mpr
    simpa only [Function.comp_def, inherited_row] using hs c
  · have hr := GradeCutLayerRows.cast_respects (added_index D hA v).symm
      (ladder_respects hA hp hinput v)
    convert hr using 1
    exact funext (row_added D sem hA field fields hp v)

theorem coded (hs : sem.IsCoded) : (rows₀₀).IsCoded := by
  intro c d
  rcases cell_cases c with ⟨c, rfl⟩ | ⟨v, rfl⟩
  · obtain ⟨d, rfl⟩ := (ownerEquiv₀ c).surjective d
    rw [inherited_row]
    simpa only [CellScheme.grade, old_index] using hs c d
  · rw [row_added]
    simpa only [CellScheme.grade, added_index, ladderRow, image] using
      SupportLadderRows.source_coded (ceiling₀ v)
        (rankIndex D hA field fields (SupportLadderRows.parent v) d.1)

