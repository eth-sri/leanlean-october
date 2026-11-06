/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutPairCarrier
public import VaughtConjecture.Knight.GradeCutLayerRows

/-! # Literal row splice around two lower controller layers

Higher proper owners keep their entire original rows. Both lower controller
layers keep their already constructed rows, on exactly the same lower domains.
The overlap equation concerns existing inherited rows, not future locality.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GradeCutPairRows
open Transform Value ExtOrd GradeCutPairCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
  (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j ≤ k)
  (sem : Semantics D) (low : Semantics (small D Q R j k hj hjA hk hkA))

local notation "E'" => enlarged D Q R j k hj hjA hk hkA
local notation "Ebelow" => CellScheme.below (enlarged D Q R j k hj hjA hk hkA)
local notation "Ecell" => CellScheme.cell (enlarged D Q R j k hj hjA hk hkA)
local notation "Egrade" => CellScheme.grade (enlarged D Q R j k hj hjA hk hkA)
local notation "S'" => small D Q R j k hj hjA hk hkA
local notation "Sbelow" => CellScheme.below (small D Q R j k hj hjA hk hkA)
local notation "Scell" => CellScheme.cell (small D Q R j k hj hjA hk hkA)
local notation "Sgrade" => CellScheme.grade (small D Q R j k hj hjA hk hkA)
local notation "B'" => GradeCutBoundary.scheme D k
local notation "Bbelow" => CellScheme.below (GradeCutBoundary.scheme D k)
local notation "Bcell" => CellScheme.cell (GradeCutBoundary.scheme D k)
local notation "belowEquiv'" => belowEquiv D Q R j k hj hjA hk hkA
local notation "properEquiv'" => properEquiv D Q R j k hj hjA hk hkA
local notation "occEquiv'" => occEquiv D Q R j k hj hjA hk hkA
local notation "occSymm" => Equiv.symm (occEquiv D Q R j k hj hjA hk hkA)
local notation "occSurj" => Equiv.surjective (occEquiv D Q R j k hj hjA hk hkA)
local notation "cell'" => cell D Q R j k hj hjA hk hkA
local notation "old'" => old D Q R j k hj hjA hk hkA
local notation "embed'" => embed D Q R j k hj hjA hk hkA
local notation "cell_idx'" => cell_idx D Q R j k hj hjA hk hkA
local notation "embed_index'" => embed_index D Q R j k hj hjA hk hkA
local notation "embed_cell'" => embed_cell D Q R j k hj hjA hk hkA
local notation "small_grade'" => small_grade D Q R j k hj hjA hk hkA hjk
local notation "cellB'" => cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA
local notation "oldB'" => old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

def ownerEquiv (c : Cell D) :=
  properEquiv' (D.cell c) (GradeCutLayerRows.proper_scope D hp c)

local notation "ownerEquiv'" => ownerEquiv D Q R j k hj hjA hk hkA hp

def liftedRow (c : Cell S') : Ebelow (Scell c) → ExtOrd :=
  low.E c ∘ (belowEquiv' _ (small_grade' c)).symm

local notation "liftedRow'" => liftedRow D Q R j k hj hjA hk hkA hjk low

theorem liftedRow_orderly (c : Cell S') (d : Ebelow (Scell c)) :
    SelfVis (Egrade d.1) (liftedRow' c d) := by
  let e := belowEquiv' _ (small_grade' c)
  have he : embed' (e.symm d).1 = d.1 := congrArg Subtype.val (e.apply_symm_apply d)
  have hg : Egrade d.1 = Sgrade (e.symm d).1 := by
    rw [← he]; exact congrArg Prod.snd (embed_index' (e.symm d).1)
  rw [hg]
  exact (low.orderly c (e.symm d)).symm

def rowAt (x : (Cell D ⊕ Q) ⊕ R) : Ebelow (idx D Q R j k x) → ExtOrd :=
  match x with
  | .inl (.inl c) => sem.E c ∘ (ownerEquiv' c).symm
  | .inl (.inr q) => fun d =>
      liftedRow' (cellB' (.inl (.inr q)))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
  | .inr r => fun d =>
      liftedRow' (cellB' (.inr r))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩

local notation "rowAt'" => rowAt D Q R j k hj hjA hk hkA hp hjk sem low

def rows : Semantics E' where
  E c d := rowAt' (occSymm c)
    ⟨d.1, by
      have he : Ecell (occEquiv' (occSymm c)) = _ := cell_idx' (occSymm c)
      rw [Equiv.apply_symm_apply] at he
      exact he ▸ d.2⟩
  orderly _ _ := by
    have h (x) (d) : SelfVis (Egrade d.1) (rowAt' x d) := by
      rcases x with (c | q) | r
      · let e := ownerEquiv' c
        have he : old' (e.symm d).1 = d.1 := congrArg Subtype.val (e.apply_symm_apply d)
        have hg : Egrade d.1 = D.grade (e.symm d).1 := by
          rw [← he]; exact congrArg Prod.snd (cell_idx' (.inl (.inl (e.symm d).1)))
        rw [hg]
        exact (sem.orderly c (e.symm d)).symm
      · exact liftedRow_orderly D Q R j k hj hjA hk hkA hjk low (cellB' (.inl (.inr q))) _
      · exact liftedRow_orderly D Q R j k hj hjA hk hkA hjk low (cellB' (.inr r)) _
    exact (h _ _).symm

local notation "rows'" => rows D Q R j k hj hjA hk hkA hp hjk sem low
local notation "rowsE" => Semantics.E (rows D Q R j k hj hjA hk hkA hp hjk sem low)

theorem rowAt_congr {x y : (Cell D ⊕ Q) ⊕ R} (hxy : x = y)
    {d : Ebelow (idx D Q R j k x)} {e : Ebelow (idx D Q R j k y)} (hde : d.1 = e.1) :
    rowAt' x d = rowAt' y e := by
  subst hxy; rw [Subtype.ext hde]

theorem rows_cell (x : (Cell D ⊕ Q) ⊕ R) (d : Ebelow (Ecell (cell' x))) :
    rowsE (cell' x) d = rowAt' x ⟨d.1, by simpa only [cell_idx] using d.2⟩ :=
  rowAt_congr D Q R j k hj hjA hk hkA hp hjk sem low (Equiv.symm_apply_apply occEquiv' x) rfl

local notation "rows_cell'" => rows_cell D Q R j k hj hjA hk hkA hp hjk sem low

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    rowsE (old' c)
      ⟨(ownerEquiv' c d).1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using (ownerEquiv' c d).2⟩ =
    sem.E c d :=
  (rows_cell' (.inl (.inl c)) _).trans (congrArg (sem.E c) ((ownerEquiv' c).symm_apply_apply d))

local notation "old_row'" => old_row D Q R j k hj hjA hk hkA hp hjk sem low

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D k))
    (d : (GradeCutBoundary.scheme D k).below ((GradeCutBoundary.scheme D k).cell c)),
    low.E (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c)
      ⟨old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA d.1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩ =
      (GradeCutBoundary.rows D k sem).E c d)

include hmatch in
theorem embedded_row (c : Cell S') (d : Sbelow (Scell c)) :
    rowsE (embed' c) ⟨embed' d.1, by simpa only [embed_index] using d.2⟩ = low.E c d := by
  obtain ⟨x, rfl⟩ := (occEquiv B' Q R j k hj hjA hk hkA).surjective c
  change rowsE (embed' (cellB' x)) _ = _
  have helper (a : Cell S') (e : Sbelow (Scell a)) :
      liftedRow' a ⟨embed' e.1, by simpa only [embed_index] using e.2⟩ = low.E a e :=
    congrArg (low.E a) ((belowEquiv' _ (small_grade' a)).symm_apply_apply e)
  rcases x with (c | q) | r
  · let ep := properEquiv B' Q R j k hj hjA hk hkA (Bcell c)
      (GradeCutLayerRows.proper_scope D hp (GradeCutBoundary.toCell D k c))
    obtain ⟨e, he⟩ := ep.surjective ⟨d.1, by
      have hd : GradedLe _ (Scell (cellB' (.inl (.inl c)))) := d.2
      simpa only [cell_idx, GradeCutPairCarrier.idx] using hd⟩
    have hev : oldB' e.1 = d.1 := congrArg Subtype.val he
    refine (Semantics.E_congr' _ (embed_cell' (.inl (.inl c)))
      ((congrArg embed' hev).symm.trans (embed_cell' (.inl (.inl e.1))))).trans
      ((old_row' (GradeCutBoundary.toCell D k c)
        (GradeCutBoundary.belowEquiv D k _ (GradeCutBoundary.grade_bound D k c) e)).trans
        ((hmatch c e).symm.trans (low.E_congr' rfl hev)))
  · refine (Semantics.E_congr' _ (embed_cell' (.inl (.inr q)))
      (d' := ⟨embed' d.1, by
        rw [embed_index, cell_idx]
        have hd : GradedLe _ (Scell (cellB' (.inl (.inr q)))) := d.2
        rw [cell_idx] at hd; exact hd⟩) rfl).trans
      ((rows_cell' (.inl (.inr q)) _).trans (helper _ d))
  · refine (Semantics.E_congr' _ (embed_cell' (.inr r))
      (d' := ⟨embed' d.1, by
        rw [embed_index, cell_idx]
        have hd : GradedLe _ (Scell (cellB' (.inr r))) := d.2
        rw [cell_idx] at hd; exact hd⟩) rfl).trans
      ((rows_cell' (.inr r) _).trans (helper _ d))

local notation "embedded_row'" => embedded_row D Q R j k hj hjA hk hkA hp hjk sem low hmatch

theorem proper_respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow rows' BJ (p ∘ (properEquiv' BJ hB).symm) := by
  apply respects_iff_of_equiv (properEquiv' BJ hB)
    (fun d => (congrArg Prod.snd (cell_idx' (.inl (.inl d.1)))).symm)
    (fun d e => ?_)
    (fun b d _ => (old_row' b.1 d).symm) p
  change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔ (Ecell (old' d.1)).1 ⊆ (Ecell (old' e.1)).1
  simp only [old, cell_idx, GradeCutPairCarrier.idx]

local notation "proper_respects_iff'" => proper_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low

include hmatch in
theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) (p : Sbelow BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow rows' BJ (p ∘ (belowEquiv' BJ hBJ).symm) := by
  apply respects_iff_of_equiv (belowEquiv' BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_index' d.1)).symm)
    (fun d e => ?_)
    (fun b d _ => (embedded_row' b.1 d).symm) p
  change (Scell d.1).1 ⊆ (Scell e.1).1 ↔ (Ecell (embed' d.1)).1 ⊆ (Ecell (embed' e.1)).1
  simp only [embed_index]

local notation "lower_respects_iff'" =>
  lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch

include hmatch in
theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    Semantics.IsConsistent rows' := by
  let P a := RespectsSemanticsBelow rows' (Ecell a) (rowsE a)
  have hold (c : Cell D) : P (old' c) := by
    have hu := GradeCutLayerRows.cast_respects _ _ (cell_idx' (.inl (.inl c))).symm
      ((proper_respects_iff' (D.cell c) (GradeCutLayerRows.proper_scope D hp c) _).mp (hs c))
    convert hu using 1
    funext d
    let e := ownerEquiv' c
    let d' : Ebelow (D.cell c) :=
      ⟨d.1, by simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    have he := congrArg Subtype.val (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans (old_row' c (e.symm d'))
  have hlow (c : Cell S') : P (embed' c) := by
    have hu := GradeCutLayerRows.cast_respects _ _ (embed_index' c).symm
      ((lower_respects_iff' _ (small_grade' c) _).mp (hl c))
    convert hu using 1
    funext d
    let e := belowEquiv' _ (small_grade' c)
    let d' : Ebelow (Scell c) := ⟨d.1, by simpa only [embed_index] using d.2⟩
    have he := congrArg Subtype.val (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans (embedded_row' c (e.symm d'))
  intro c
  obtain ⟨(d | q) | r, rfl⟩ := occSurj c
  · exact hold d
  · exact (congrArg P (embed_cell' (.inl (.inr q)))).mp (hlow (cellB' (.inl (.inr q))))
  · exact (congrArg P (embed_cell' (.inr r))).mp (hlow (cellB' (.inr r)))

def glue (p : Cell D → ExtOrd) (r : Cell S' → ExtOrd) (d : Cell E') : ExtOrd :=
  match occSymm d with
  | .inl (.inl a) => p a
  | .inl (.inr q) => r (cellB' (.inl (.inr q)))
  | .inr q => r (cellB' (.inr q))

local notation "glue'" => glue D Q R j k hj hjA hk hkA

theorem glue_old (p : Cell D → ExtOrd) (r : Cell S' → ExtOrd) (d : Cell D) :
    glue' p r (old' d) = p d := by
  simp only [glue, old, cell, Equiv.symm_apply_apply]

local notation "glue_old'" => glue_old D Q R j k hj hjA hk hkA

theorem glue_embed (p : Cell D → ExtOrd) (r : Cell S' → ExtOrd)
    (hag : ∀ c, r (oldB' c) = p (GradeCutBoundary.toCell D k c)) (d : Cell S') :
    glue' p r (embed' d) = r d := by
  obtain ⟨x, rfl⟩ := (occEquiv B' Q R j k hj hjA hk hkA).surjective d
  change glue' p r (embed' (cellB' x)) = _
  rw [embed_cell]
  rcases x with (d | q) | q
  · exact (glue_old' p r _).trans (hag d).symm
  · simp only [Sum.map_inl, Sum.map_inr, id_eq, glue, cell, Equiv.symm_apply_apply]
  · simp only [Sum.map_inr, id_eq, glue, cell, Equiv.symm_apply_apply]

include hmatch in
theorem glue_respects {p : Cell D → ExtOrd} {r : Cell S' → ExtOrd}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (oldB' c) = p (GradeCutBoundary.toCell D k c)) :
    RespectsSemantics rows' (glue' p r) := by
  apply GradeCutLayerRows.respects_of_lower
  intro c
  obtain ⟨x, rfl⟩ := occSurj c
  change RespectsSemanticsBelow rows' (Ecell (cell' x)) _
  have hlow (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) :
      RespectsSemanticsBelow rows' BJ (fun d => glue' p r d.1) := by
    have ht := (lower_respects_iff' BJ hBJ _).mp (hr.toBelow BJ)
    convert ht using 1
    funext d
    exact (congrArg (glue' p r)
      (congrArg Subtype.val ((belowEquiv' BJ hBJ).apply_symm_apply d))).symm.trans
        (glue_embed D Q R j k hj hjA hk hkA p r hag _)
  rcases x with (a | q) | q
  · refine (congrArg (RespectsSemanticsBelow rows' _) (funext fun d => ?_)).mpr
      (GradeCutLayerRows.cast_respects _ _ (cell_idx' (.inl (.inl a))).symm
        ((proper_respects_iff' (D.cell a)
          (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.toBelow (D.cell a))))
    let d' : Ebelow (D.cell a) :=
      ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    exact (congrArg (glue' p r)
      (congrArg Subtype.val ((ownerEquiv' a).apply_symm_apply d'))).symm.trans
        (glue_old' p r _)
  · exact hlow _ (by rw [cell_idx]; exact hjk)
  · exact hlow _ (by rw [cell_idx]; exact le_rfl)

