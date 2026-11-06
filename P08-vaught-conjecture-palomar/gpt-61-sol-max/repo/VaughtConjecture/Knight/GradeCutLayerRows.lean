
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutLayerCarrier

/-! # Literal row splice at a grade cut

Retain all proper boundary rows, including higher-grade and long rows. The
full-scope rows already constructed on the smaller grade cut are transported
across their exact lower domains; their source values are not renormalized.
-/

namespace VaughtConjecture.Knight.GradeCutLayerRows

open  Value  SourceLayerCarrier GradeCutLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (j : ℕ)
variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hp : AvoidsValue D.scope A)
variable (sem : Semantics D) (low : Semantics (small D Q j hj hA))

include hp in
theorem proper_scope c : ¬ A ⊆ D.scope c := by
  intro hc
  exact hp c (Finset.Subset.antisymm (D.scope_subset c) hc)

def oldBelow c := properEquiv D Q j hj hA (D.cell c) (proper_scope D hp c)

local notation "belowEquiv₀" => belowEquiv (A, j) le_rfl

local notation "enlarged₀" => enlarged D Q j hj hA

local notation "oldBelow₀" => oldBelow D Q j hj hA hp

local notation "toCell₀" => toCell (GradeCutBoundary.scheme D j) Q j hj hA

def rowAt x : (enlarged₀).below (index D Q j x) → ExtOrd :=
  match x with
  | .inl c => fun d => sem.E c ((oldBelow₀ c).symm d)
  | .inr q => fun d => low.E (toCell₀ (.inr q))
      ⟨((belowEquiv₀).symm d).1, by
        simpa only [cell_toCell, index] using
          ((belowEquiv₀).symm d).2⟩

local notation "toCell₀₀" => toCell D Q j hj hA

theorem oldBelow_cell c d :
    D.cell ((oldBelow₀ c).symm d).1 =
      (enlarged₀).cell d.1 := by
  have he := congrArg Subtype.val ((oldBelow₀ c).apply_symm_apply d)
  change toCell₀₀ (.inl _) = d.1 at he
  rw [← he, cell_toCell]
  rfl

local notation "embed₀" => embed D Q j hj hA

local notation "small₀" => small D Q j hj hA

theorem lowBelow_cell d :
    (small₀).cell ((belowEquiv₀).symm d).1 =
      (enlarged₀).cell d.1 := by
  have he := congrArg Subtype.val
    ((belowEquiv₀).apply_symm_apply d)
  change embed₀ _ = d.1 at he
  rw [← he, embed_cell]

local notation "rowAt₀" => rowAt D Q j hj hA hp sem low

theorem rowAt_orderly x
    d :
    rowAt₀ x d =
      extVisibilityReplace (rowAt₀ x d)
        ((enlarged₀).grade d.1) ((enlarged₀).grade d.1) := by
  cases x with
  | inl a =>
    have hv := sem.orderly a ((oldBelow₀ a).symm d)
    have hg := congrArg Prod.snd (oldBelow_cell D Q j hj hA hp a d)
    
    exact hv.trans (congrArg (fun i => extVisibilityReplace _ i i) hg)
  | inr q =>
    have hv := low.orderly (toCell₀ (.inr q))
      ⟨((belowEquiv₀).symm d).1, by
        rw [cell_toCell]
        exact ((belowEquiv₀).symm d).2⟩
    have hg := congrArg Prod.snd (lowBelow_cell D Q j hj hA d)
    
    exact hv.trans (congrArg (fun i => extVisibilityReplace _ i i) hg)

variable {D Q j hj hA} in
def rows : Semantics (enlarged₀) where
  E c d := rowAt₀ (toOcc D Q j hj hA c)
    ⟨d.1, by simpa only [← cell_eq] using d.2⟩
  orderly c d := rowAt_orderly D Q j hj hA hp sem low _ _

theorem rowAt_congr {x y} (hxy : x = y)
    {d : (enlarged₀).below (index D Q j x)}
    {e : (enlarged₀).below (index D Q j y)} (hde : d.1 = e.1) :
    rowAt₀ x d = rowAt₀ y e := by
  subst y
  rw [Subtype.ext hde]

local notation "rows₀" => rows hp sem low

theorem rows_toCell x
    d :
    (rows₀).E (toCell₀₀ x) d =
      rowAt₀ x
        ⟨d.1, by simpa only [cell_toCell] using d.2⟩ :=
  rowAt_congr D Q j hj hA hp sem low (toOcc_toCell D Q j hj hA x) rfl

local notation "ownerEquiv₀" => ownerEquiv hj hA hp

theorem old_row c d :
    (rows₀).E (toCell₀₀ (.inl c))
      (ownerEquiv₀ c d) = sem.E c d := by
  rw [rows_toCell]
  change sem.E c ((oldBelow₀ c).symm ((oldBelow₀ c) d)) = _
  rw [Equiv.symm_apply_apply]

theorem controller_row q
    (d : (small₀).below (A, j)) :
    (rows₀).E (toCell₀₀ (.inr q))
      ⟨embed₀ d.1, by
        rw [cell_toCell, embed_cell]; exact d.2⟩ =
    low.E (toCell₀ (.inr q))
      ⟨d.1, by rw [cell_toCell]; exact d.2⟩ := by
  refine (rows_toCell D Q j hj hA hp sem low (.inr q) _).trans ?_
  apply low.E_congr' rfl
  exact congrArg (fun z => z.1)
    ((belowEquiv₀).symm_apply_apply d)

variable {D Q j hj hA hp sem low} in
theorem old_respects_iff c
    p :
    RespectsSemanticsBelow (rows hp sem low) _ p ↔
      Semantics.RowLawful sem c (p ∘ ownerEquiv₀ c) := by
  have ht := respects_iff_of_equiv  
    (ownerEquiv₀ c)
    (fun d => (congrArg Prod.snd (cell_toCell D Q j hj hA (.inl d.1))).symm)
    (fun d e => by
      change D.scope d.1 ⊆ D.scope e.1 ↔
        ((enlarged₀).cell (toCell₀₀ (.inl d.1))).1 ⊆
        ((enlarged₀).cell (toCell₀₀ (.inl e.1))).1
      rw [cell_toCell, cell_toCell]; rfl)
    (fun b d _ => (old_row D Q j hj hA hp sem low b.1 d).symm)
    (p ∘ ownerEquiv₀ c)
  have he : (p ∘ ownerEquiv₀ c) ∘
      (ownerEquiv₀ c).symm = p := by
    grind
  rw [he] at ht
  exact ht.symm

variable (hmatch : ∀ c
  d,
  low.E (toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inl c))
    (ownerEquiv hj hA (GradeCutBoundary.proper hp) c d) =
  (GradeCutBoundary.rows D j sem).E c d)

include hmatch

theorem embedded_row c
    (d : (small₀).belowCell c) :
    (rows₀).E (embed₀ c)
      ⟨embed₀ d.1, by simpa only [embed_cell] using d.2⟩ = low.E c d := by 
  obtain ⟨x, rfl⟩ := (enumeration).surjective c
  let core1 := embed_toCell D Q j hj hA
  cases x with
  | inl a =>
    obtain ⟨e, rfl⟩ := (ownerEquiv hj hA
      (GradeCutBoundary.proper hp) a).surjective d
    have he := old_row D Q j hj hA hp sem low (GradeCutBoundary.toCell D j a)
      (GradeCutBoundary.belowEquiv D ((GradeCutBoundary.scheme D j).cell a)
        (GradeCutBoundary.grade_bound a) e)
    refine (Semantics.E_congr' _ (core1 (.inl a)) ?_).trans
      (he.trans (hmatch a e).symm)
    exact core1 (.inl e.1)
  | inr q =>
    let e : (small₀).below (A, j) :=
      ⟨d.1, by
        have hc := d.2
        change GradedLe ((small₀).cell d.1)
          ((small₀).cell
            (toCell₀ (.inr q))) at hc
        rwa [cell_toCell] at hc⟩
    exact (Semantics.E_congr' _ (core1 (.inr q)) rfl).trans
      (controller_row D Q j hj hA hp sem low q e)

theorem lower_respects_iff (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ j)
    p :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows₀) BJ
        (p ∘ (belowEquiv BJ hBJ).symm) :=
  respects_iff_of_equiv (belowEquiv BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_cell D Q j hj hA d.1)).symm)
    (fun d e => by
      change ((small₀).cell d.1).1 ⊆ ((small₀).cell e.1).1 ↔
        ((enlarged₀).cell (embed₀ d.1)).1 ⊆
        ((enlarged₀).cell (embed₀ e.1)).1
      rw [embed_cell, embed_cell])
    (fun b d _ => (embedded_row D Q j hj hA hp sem low hmatch b.1 d).symm) p

omit hmatch in
variable {D sem} in
theorem cast_respects {B C} (h : B = C)
    {p} (hr : RespectsSemanticsBelow sem B p) :
    RespectsSemanticsBelow sem C (fun d => p ⟨d.1, h.symm ▸ d.2⟩) := by
  subst C
  exact hr

theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows₀).IsConsistent := by
  intro c
  obtain ⟨x, rfl⟩ := (enumeration).surjective c
  cases x with
  | inl a =>
    apply (old_respects_iff a _).mpr
    change Semantics.RowLawful sem a (fun d =>
      (rows₀).E (toCell₀₀ (.inl a))
        (ownerEquiv₀ a d))
    simpa only [old_row] using hs a
  | inr q =>
    have hc := cast_respects
      (cell_toCell (GradeCutBoundary.scheme D j) Q j hj hA (.inr q))
      (hl (toCell₀ (.inr q)))
    have ht := (lower_respects_iff D Q j hj hA hp sem low hmatch (A, j) le_rfl _).mp
      hc
    have hu := cast_respects
      (cell_toCell D Q j hj hA (.inr q)).symm ht
    convert hu using 1 <;> try rfl
    apply heq_of_eq
    funext d
    exact rows_toCell D Q j hj hA hp sem low (.inr q) d

omit hmatch in
theorem respects_of_lower {p}
    (hr : ∀ c, Semantics.RowLawful sem c (fun d => p d.1)) :
    RespectsSemantics sem p where
  orderly c := (hr c).orderly ⟨c, GradedLe.refl _⟩
  locality c := (hr c).locality ⟨c, GradedLe.refl _⟩
  availability c t hs hg := by
    obtain ⟨w, hw, hb⟩ := (hr t).availability ⟨c, hs, hg.le⟩
      ⟨t, GradedLe.refl _⟩ hs hg
    exact ⟨w.1, hw, hb⟩

omit hmatch in
def glue (p : CellLabels D) (r : CellLabels (small₀))
    (d : Cell (enlarged₀)) :=
  match toOcc D Q j hj hA d with
  | .inl c => p c
  | .inr q => r (toCell₀ (.inr q))

local notation "glue₀" => glue D Q j hj hA

omit hmatch in
theorem glue_old p r
    c : glue₀ p r (toCell₀₀ (.inl c)) = p c := by
  simp  [glue, ]

omit hmatch in
theorem glue_embed p r
    (hr : ∀ c, r (toCell₀ (.inl c)) =
      p (GradeCutBoundary.toCell D j c)) c :
    glue₀ p r (embed₀ c) = r c := by
  obtain ⟨x, rfl⟩ := (enumeration).surjective c
  change glue₀ p r (embed₀
    (toCell₀ x)) = _
  rw [embed_toCell]
  cases x with
  | inl c => exact (glue_old D Q j hj hA p r _).trans (hr c).symm
  | inr q =>
    simp_all  [glue] <;> aesop

theorem glue_respects {p} {r}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (toCell₀ (.inl c)) =
      p (GradeCutBoundary.toCell D j c)) :
    RespectsSemantics (rows₀) (glue₀ p r) := by
  apply respects_of_lower
  intro c
  obtain ⟨x, rfl⟩ := (enumeration).surjective c
  cases x with
  | inl a =>
    apply (old_respects_iff a _).mpr
    change Semantics.RowLawful sem a
      (fun d => glue₀ p r (toCell₀₀ (.inl d.1)))
    simpa only [glue_old] using hpr.toBelow (D.cell a)
  | inr q =>
    let BJ := (enlarged₀).cell (toCell₀₀ (.inr q))
    have hBJ : BJ.2 ≤ j := by dsimp only [BJ]; rw [cell_toCell]; exact le_rfl
    have ht := (lower_respects_iff D Q j hj hA hp sem low hmatch BJ hBJ _).mp (hr.toBelow BJ)
    
    have heq : (fun d => glue₀ p r d.1) =
        (fun d => r d.1) ∘
          (belowEquiv BJ hBJ).symm := by
      funext d
      have he := congrArg (fun z => z.1)
        ((belowEquiv BJ hBJ).apply_symm_apply d)
      exact (congrArg (glue₀ p r) he).symm.trans
        (glue_embed D Q j hj hA p r hag _)
    exact heq.symm ▸ ht

