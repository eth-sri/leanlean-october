/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeCutLayerCarrier

/-! # Literal row splice at a grade cut

Retain all proper boundary rows, including higher-grade and long rows. The
full-scope rows already constructed on the smaller grade cut are transported
across their exact lower domains; their source values are not renormalized.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GradeCutLayerRows

open Transform Value ExtOrd SourceLayerCarrier GradeCutLayerCarrier

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
  (hj : 0 < j) (hA : j ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (sem : Semantics D) (low : Semantics (small D Q j hj hA))

local notation "E'" => enlarged D Q j hj hA
local notation "Ebelow" => CellScheme.below (enlarged D Q j hj hA)
local notation "Ecell" => CellScheme.cell (enlarged D Q j hj hA)
local notation "Egrade" => CellScheme.grade (enlarged D Q j hj hA)
local notation "S'" => small D Q j hj hA
local notation "Sbelow" => CellScheme.below (small D Q j hj hA)
local notation "Scell" => CellScheme.cell (small D Q j hj hA)
local notation "B'" => GradeCutBoundary.scheme D j
local notation "belowEquiv'" => belowEquiv D Q j hj hA
local notation "toCell'" => toCell D Q j hj hA
local notation "toOcc'" => toOcc D Q j hj hA
local notation "cell_toCell'" => cell_toCell D Q j hj hA
local notation "embed'" => embed D Q j hj hA
local notation "embed_cell'" => embed_cell D Q j hj hA
local notation "embed_toCell'" => embed_toCell D Q j hj hA
local notation "ownerEquiv'" => ownerEquiv D Q j hj hA hp
local notation "toCellB'" => toCell (GradeCutBoundary.scheme D j) Q j hj hA

include hp in
theorem proper_scope (c : Cell D) : ¬ A ⊆ D.scope c := fun hc =>
  hp c (Finset.Subset.antisymm (D.isPlan.subset_of_mem (D.scope_mem_plan c)) hc)

def oldBelow (c : Cell D) := properEquiv D Q j hj hA (D.cell c) (proper_scope D hp c)

local notation "oldBelow'" => oldBelow D Q j hj hA hp

def rowAt (x : Cell D ⊕ Q) : Ebelow (index D Q j x) → ExtOrd :=
  match x with
  | .inl c => fun d => sem.E c ((oldBelow' c).symm d)
  | .inr q => fun d => low.E (toCellB' (.inr q))
      ⟨((belowEquiv' (A, j) le_rfl).symm d).1, by
        simpa only [cell_toCell, index] using ((belowEquiv' (A, j) le_rfl).symm d).2⟩

local notation "rowAt'" => rowAt D Q j hj hA hp sem low

def rows : Semantics E' where
  E c d := rowAt' (toOcc' c) ⟨d.1, by simpa only [← cell_eq] using d.2⟩
  orderly c d := by
    have h (x) (d : Ebelow (index D Q j x)) :
        rowAt' x d = extVisibilityReplace (rowAt' x d) (Egrade d.1) (Egrade d.1) := by
      cases x with
      | inl a =>
        have he : toCell' (.inl _) = d.1 := congrArg Subtype.val ((oldBelow' a).apply_symm_apply d)
        have hg : D.grade ((oldBelow' a).symm d).1 = Egrade d.1 := by
          change (D.cell _).2 = (Ecell d.1).2; rw [← he, cell_toCell]; rfl
        exact (sem.orderly a ((oldBelow' a).symm d)).trans
          (congrArg (fun i => extVisibilityReplace _ i i) hg)
      | inr q =>
        have he : embed' _ = d.1 :=
          congrArg Subtype.val ((belowEquiv' (A, j) le_rfl).apply_symm_apply d)
        have hg : CellScheme.grade S' ((belowEquiv' (A, j) le_rfl).symm d).1 = Egrade d.1 := by
          change (Scell _).2 = (Ecell d.1).2; rw [← he, embed_cell]
        exact (low.orderly (toCellB' (.inr q))
          ⟨((belowEquiv' (A, j) le_rfl).symm d).1, by
            rw [cell_toCell]; exact ((belowEquiv' (A, j) le_rfl).symm d).2⟩).trans
          (congrArg (fun i => extVisibilityReplace _ i i) hg)
    exact h _ _

local notation "rows'" => rows D Q j hj hA hp sem low
local notation "rowsE" => Semantics.E (rows D Q j hj hA hp sem low)

theorem rowAt_congr {x y : Cell D ⊕ Q} (hxy : x = y)
    {d : Ebelow (index D Q j x)} {e : Ebelow (index D Q j y)} (hde : d.1 = e.1) :
    rowAt' x d = rowAt' y e := by
  subst y; rw [Subtype.ext hde]

theorem rows_toCell (x : Cell D ⊕ Q) (d : Ebelow (Ecell (toCell' x))) :
    rowsE (toCell' x) d = rowAt' x ⟨d.1, by simpa only [cell_toCell] using d.2⟩ :=
  rowAt_congr D Q j hj hA hp sem low (toOcc_toCell D Q j hj hA x) rfl

local notation "rows_toCell'" => rows_toCell D Q j hj hA hp sem low

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    rowsE (toCell' (.inl c)) (ownerEquiv' c d) = sem.E c d := by
  rw [rows_toCell]
  change sem.E c ((oldBelow' c).symm (oldBelow' c d)) = _
  rw [Equiv.symm_apply_apply]

local notation "old_row'" => old_row D Q j hj hA hp sem low

theorem old_respects_iff (c : Cell D) (p : Ebelow (Ecell (toCell' (.inl c))) → ExtOrd) :
    RespectsSemanticsBelow rows' _ p ↔ RespectsSemanticsBelow sem (D.cell c) (p ∘ ownerEquiv' c) := by
  have ht := respects_iff_of_equiv (sem' := sem) (sem := rows') (ownerEquiv' c)
    (fun d => (congrArg Prod.snd (cell_toCell' (.inl d.1))).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔ (Ecell (toCell' (.inl d.1))).1 ⊆ (Ecell (toCell' (.inl e.1))).1
      rw [cell_toCell, cell_toCell]; rfl)
    (fun b d _ => (old_row' b.1 d).symm) (p ∘ ownerEquiv' c)
  have he : (p ∘ ownerEquiv' c) ∘ (ownerEquiv' c).symm = p :=
    funext fun d => by simp only [Function.comp_apply, Equiv.apply_symm_apply]
  exact (he ▸ ht).symm

local notation "old_respects_iff'" => old_respects_iff D Q j hj hA hp sem low

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D j))
  (d : (GradeCutBoundary.scheme D j).below ((GradeCutBoundary.scheme D j).cell c)),
  low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c))
    (ownerEquiv (GradeCutBoundary.scheme D j) Q j hj hA (GradeCutBoundary.proper D j hp) c d) =
  (GradeCutBoundary.rows D j sem).E c d)

include hmatch

theorem embedded_row (c : Cell S') (d : Sbelow (Scell c)) :
    rowsE (embed' c) ⟨embed' d.1, by simpa only [embed_cell] using d.2⟩ = low.E c d := by
  obtain ⟨a | q, rfl⟩ := (enumeration B' Q j hj hA).surjective c
  · obtain ⟨e, rfl⟩ := (ownerEquiv B' Q j hj hA (GradeCutBoundary.proper D j hp) a).surjective d
    exact (Semantics.E_congr' _ (embed_toCell' (.inl a)) (embed_toCell' (.inl e.1))).trans
      ((old_row' (GradeCutBoundary.toCell D j a)
        (GradeCutBoundary.belowEquiv D j (CellScheme.cell B' a) (GradeCutBoundary.grade_bound D j a) e)).trans
        (hmatch a e).symm)
  · let e : Sbelow (A, j) :=
      ⟨d.1, by
        have hc : GradedLe (Scell d.1) (Scell (toCellB' (.inr q))) := d.2
        rwa [cell_toCell] at hc⟩
    have hev := congrArg Subtype.val ((belowEquiv' (A, j) le_rfl).symm_apply_apply e)
    exact (Semantics.E_congr' _ (embed_toCell' (.inr q))
      (d' := ⟨embed' d.1, by rw [cell_toCell, embed_cell]; exact e.2⟩) rfl).trans
      ((rows_toCell' (.inr q) _).trans (low.E_congr' rfl hev))

theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ j) (p : Sbelow BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow rows' BJ (p ∘ (belowEquiv' BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv' BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_cell' d.1)).symm)
    (fun d e => by
      change (Scell d.1).1 ⊆ (Scell e.1).1 ↔ (Ecell (embed' d.1)).1 ⊆ (Ecell (embed' e.1)).1
      rw [embed_cell, embed_cell])
    (fun b d _ => (embedded_row D Q j hj hA hp sem low hmatch b.1 d).symm) p

local notation "lower_respects_iff'" => lower_respects_iff D Q j hj hA hp sem low hmatch

omit hmatch in
theorem cast_respects {B C : Finset ι × ℕ} (h : B = C)
    {p : D.below B → ExtOrd} (hr : RespectsSemanticsBelow sem B p) :
    RespectsSemanticsBelow sem C (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := by
  subst C; exact hr

theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    Semantics.IsConsistent rows' := by
  intro c
  obtain ⟨a | q, rfl⟩ := (enumeration D Q j hj hA).surjective c
  · apply (old_respects_iff' a _).mpr
    change RespectsSemanticsBelow sem (D.cell a) (fun d => rowsE (toCell' (.inl a)) (ownerEquiv' a d))
    simpa only [old_row] using hs a
  · have hu := cast_respects E' rows' (cell_toCell' (.inr q)).symm
      ((lower_respects_iff' (A, j) le_rfl _).mp
        (cast_respects S' low (cell_toCell B' Q j hj hA (.inr q)) (hl (toCellB' (.inr q)))))
    convert hu using 1 <;> try rfl
    exact heq_of_eq (funext (rows_toCell' (.inr q)))

omit hmatch in
theorem respects_of_lower {p : Cell D → ExtOrd}
    (hr : ∀ c, RespectsSemanticsBelow sem (D.cell c) (fun d => p d.1)) :
    RespectsSemantics sem p where
  orderly c := (hr c).orderly ⟨c, GradedLe.refl _⟩
  locality c := (hr c).locality ⟨c, GradedLe.refl _⟩
  availability c t hs hg :=
    let ⟨w, hw, hb⟩ := (hr t).availability ⟨c, hs, hg.le⟩ ⟨t, GradedLe.refl _⟩ hs hg
    ⟨w.1, hw, hb⟩

omit hmatch in
def glue (p : Cell D → ExtOrd) (r : Cell S' → ExtOrd) (d : Cell E') : ExtOrd :=
  match toOcc' d with
  | .inl c => p c
  | .inr q => r (toCellB' (.inr q))

local notation "glue'" => glue D Q j hj hA

omit hmatch in
theorem glue_old (p : Cell D → ExtOrd) (r : Cell S' → ExtOrd) (c : Cell D) :
    glue' p r (toCell' (.inl c)) = p c := by
  simp only [glue, toOcc_toCell]

theorem glue_respects {p : Cell D → ExtOrd} {r : Cell S' → ExtOrd}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (toCellB' (.inl c)) = p (GradeCutBoundary.toCell D j c)) :
    RespectsSemantics rows' (glue' p r) := by
  apply respects_of_lower
  intro c
  obtain ⟨a | q, rfl⟩ := (enumeration D Q j hj hA).surjective c
  · apply (old_respects_iff' a _).mpr
    change RespectsSemanticsBelow sem (D.cell a) (fun d => glue' p r (toCell' (.inl d.1)))
    simpa only [glue_old] using hpr.toBelow (D.cell a)
  · let BJ := Ecell (toCell' (.inr q))
    have hBJ : BJ.2 ≤ j := by dsimp only [BJ]; rw [cell_toCell]; exact le_rfl
    have ht := (lower_respects_iff' BJ hBJ _).mp (hr.toBelow BJ)
    change RespectsSemanticsBelow rows' BJ _
    have heq : (fun d : Ebelow BJ => glue' p r d.1) =
        (fun d : Sbelow BJ => r d.1) ∘ (belowEquiv' BJ hBJ).symm := by
      funext d
      have he : embed' _ = d.1 := congrArg Subtype.val ((belowEquiv' BJ hBJ).apply_symm_apply d)
      refine (congrArg (glue' p r) he).symm.trans ?_
      change glue' p r (embed' ((belowEquiv' BJ hBJ).symm d).1) = r ((belowEquiv' BJ hBJ).symm d).1
      generalize ((belowEquiv' BJ hBJ).symm d).1 = w
      obtain ⟨c | q', rfl⟩ := (enumeration B' Q j hj hA).surjective w
      · change glue' p r (embed' (toCellB' (.inl c))) = _
        rw [embed_toCell]; exact (glue_old D Q j hj hA p r _).trans (hag c).symm
      · change glue' p r (embed' (toCellB' (.inr q'))) = _
        rw [embed_toCell]; simp only [glue, toOcc_toCell]; rfl
    exact heq.symm ▸ ht

