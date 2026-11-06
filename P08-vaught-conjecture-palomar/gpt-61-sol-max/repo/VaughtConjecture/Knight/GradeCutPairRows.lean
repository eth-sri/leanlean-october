
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.GradeCutPairCarrier
import VaughtConjecture.Knight.GradeCutLayerRows

/-! # Literal row splice around two lower controller layers

Higher proper owners keep their entire original rows. Both lower controller
layers keep their already constructed rows, on exactly the same lower domains.
The overlap equation concerns existing inherited rows, not future locality.
-/

namespace VaughtConjecture.Knight.GradeCutPairRows
open    GradeCutPairCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : AvoidsValue D.scope A) (hjk : j ≤ k)
variable (sem : Semantics D) (low : Semantics (small D Q R j k hj hjA hk hkA))

local notation "properEquiv₀" => properEquiv D Q R j k hj hjA hk hkA

def ownerEquiv c :=
  properEquiv₀ (D.cell c) (GradeCutLayerRows.proper_scope D hp c)

local notation "belowEquiv₀" => belowEquiv D Q R j k hj hjA hk hkA

local notation "enlarged₀" => enlarged D Q R j k hj hjA hk hkA

local notation "small_grade₀" => small_grade D Q R j k hj hjA hk hkA hjk

local notation "small₀" => small D Q R j k hj hjA hk hkA

def liftedRow c :=
  low.E c ∘ (belowEquiv₀ _
    (small_grade₀ c)).symm

local notation "embed_index₀" => embed_index

local notation "embed₀" => embed D Q R j k hj hjA hk hkA

local notation "liftedRow₀" => liftedRow D Q R j k hj hjA hk hkA hjk low

theorem liftedRow_orderly c
    (d : (enlarged₀).below
      ((small₀).cell c)) :
    SelfVis ((enlarged₀).grade d.1)
      (liftedRow₀ c d) := by
  let e := belowEquiv₀ _
    (small_grade₀ c)
  have he := congrArg Subtype.val (e.apply_symm_apply d)
  change embed₀ (e.symm d).1 = d.1 at he
  have hg := congrArg Prod.snd (embed_index₀ (e.symm d).1)
  rw [he] at hg
  change (enlarged₀).grade d.1 =
    (small₀).grade (e.symm d).1 at hg
  rw [hg]
  exact (low.orderly c (e.symm d)).symm

local notation "cell₀" => cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

local notation "ownerEquiv₀" => ownerEquiv D Q R j k hj hjA hk hkA hp

def rowAt x :
    (enlarged₀).below (idx D Q R j k x) → ExtOrd :=
  match x with
  | .inl (.inl c) => sem.E c ∘ (ownerEquiv₀ c).symm
  | .inl (.inr q) => fun d =>
      liftedRow₀
        (cell₀ (.inl (.inr q)))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
  | .inr r => fun d =>
      liftedRow₀
        (cell₀ (.inr r))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩

local notation "cell_idx₀" => cell_idx D Q R j k hj hjA hk hkA

local notation "old₀" => old D Q R j k hj hjA hk hkA

local notation "rowAt₀" => rowAt D Q R j k hj hjA hk hkA hp hjk sem low

theorem rowAt_orderly x
    (d : (enlarged₀).below (idx D Q R j k x)) :
    SelfVis ((enlarged₀).grade d.1)
      (rowAt₀ x d) := by
  rcases x with (c | q) | r
  · let e := ownerEquiv₀ c
    have he := congrArg Subtype.val (e.apply_symm_apply d)
    change old₀ (e.symm d).1 = d.1 at he
    have hg := congrArg Prod.snd (cell_idx₀ (.inl (.inl (e.symm d).1)))
    change (enlarged₀).grade
      (old₀ (e.symm d).1) = D.grade (e.symm d).1 at hg
    rw [he] at hg
    rw [hg]
    exact (sem.orderly c (e.symm d)).symm
  · grind [rowAt, liftedRow_orderly]
  · grind [rowAt, liftedRow_orderly]

local notation "occEquiv₀" => occEquiv D Q R j k hj hjA hk hkA

def rows : Semantics (enlarged₀) where
  E c d := rowAt₀
    ((occEquiv₀).symm c)
    ⟨d.1, by
      have he := cell_idx₀ ((occEquiv₀).symm c)
      change (enlarged₀).cell
        (occEquiv₀ ((occEquiv₀).symm c)) = _ at he
      rw [Equiv.apply_symm_apply] at he
      rw [← he]
      exact d.2⟩
  orderly c d := (rowAt_orderly D Q R j k hj hjA hk hkA hp hjk sem low _ _).symm

theorem rowAt_congr {x y} (hxy : x = y)
    {d : (enlarged₀).below (GradeCutPairCarrier.idx D Q R j k x)}
    {e : (enlarged₀).below (GradeCutPairCarrier.idx D Q R j k y)}
    (hde : d.1 = e.1) :
    rowAt₀ x d =
      rowAt₀ y e := by
  subst y
  rw [Subtype.ext hde]

local notation "cell₀₀" => cell D Q R j k hj hjA hk hkA

local notation "rows₀" => rows D Q R j k hj hjA hk hkA hp hjk sem low

theorem rows_cell x
    d :
    (rows₀).E (cell₀₀ x) d =
      rowAt₀ x
        ⟨d.1, by simpa only [cell_idx] using d.2⟩ :=
  rowAt_congr D Q R j k hj hjA hk hkA hp hjk sem low
    ((occEquiv₀).symm_apply_apply x) rfl

local notation "rows_cell₀" => rows_cell D Q R j k hj hjA hk hkA hp hjk sem low

variable {D Q R j k hj hjA hk hkA} in
theorem old_row c d :
    (rows₀).E
      (old₀ c)
      ⟨(ownerEquiv₀ c d).1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using
          (ownerEquiv₀ c d).2⟩ =
    sem.E c d := (rows_cell₀ (.inl (.inl c)) _).trans
    (congrArg (sem.E c) ((ownerEquiv₀ c).symm_apply_apply d))

variable (hmatch : ∀ c
    d,
    low.E (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c)
      ⟨old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA d.1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩ =
      (GradeCutBoundary.rows D k sem).E c d)

local notation "embed_cell₀" => embed_cell D Q R j k hj hjA hk hkA

local notation "old_row₀" => old_row hp hjk sem low

local notation "old₀₀" => old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

include hmatch in
variable {D Q R j k hj hjA hk hkA hp hjk sem low} in
theorem embedded_row c
    (d : (small₀).belowCell c) :
    (rows₀).E (embed₀ c)
      ⟨embed₀ d.1, by simpa only [embed_index] using d.2⟩ = low.E c d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective c
  
  have helper (a : Cell (small₀))
      (e : (small₀).belowCell a) :
      liftedRow₀ a
        ⟨embed₀ e.1, by simpa only [embed_index] using e.2⟩ = low.E a e :=
    congrArg (low.E a) ((belowEquiv₀ _
      (small_grade₀ a)).symm_apply_apply e)
  rcases x with (c | q) | r
  · let ep := properEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA
      ((GradeCutBoundary.scheme D k).cell c)
      (GradeCutLayerRows.proper_scope D hp (GradeCutBoundary.toCell D k c))
    let d' : (small₀).below ((GradeCutBoundary.scheme D k).cell c) :=
      ⟨d.1, by
        have hd := d.2
        change GradedLe _ ((small₀).cell
          (cell _ _ _ _ _ _ _ _ _ (.inl (.inl c)))) at hd
        simpa only [cell_idx, GradeCutPairCarrier.idx] using hd⟩
    obtain ⟨e, he⟩ := ep.surjective d'
    have hev := congrArg Subtype.val he
    
    have hr := old_row₀
      (GradeCutBoundary.toCell D k c)
      (GradeCutBoundary.belowEquiv D _ (GradeCutBoundary.grade_bound c) e)
    have hc := embed_cell₀ (.inl (.inl c))
    refine (Semantics.E_congr' _ hc ?_).trans (hr.trans ?_)
    · exact (congrArg (embed₀) hev).symm.trans
        (embed_cell₀ (.inl (.inl e.1)))
    · exact (hmatch c e).symm.trans (low.E_congr' rfl hev)
  · have hc := embed_cell₀ (.inl (.inr q))
    refine (Semantics.E_congr' _ hc
      (d' := ⟨embed₀ d.1, by
        rw [embed_index, cell_idx]
        have hd := d.2
        change GradedLe _ ((small₀).cell
          (cell _ _ _ _ _ _ _ _ _ (.inl (.inr q)))) at hd
        rw [cell_idx] at hd
        exact hd⟩) rfl).trans ?_
    exact (rows_cell₀ (.inl (.inr q)) _).trans
      (helper _ d)
  · have hc := embed_cell₀ (.inr r)
    refine (Semantics.E_congr' _ hc
      (d' := ⟨embed₀ d.1, by
        rw [embed_index, cell_idx]
        have hd := d.2
        change GradedLe _ ((small₀).cell
          (cell _ _ _ _ _ _ _ _ _ (.inr r))) at hd
        rw [cell_idx] at hd
        exact hd⟩) rfl).trans ?_
    exact (rows_cell₀ (.inr r) _).trans
      (helper _ d)

variable {D Q R j k hj hjA hk hkA} in
theorem proper_respects_iff (BJ : GradedIndex ι) (hB : ¬ A ⊆ BJ.1)
    p :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows₀) BJ
        (p ∘ (properEquiv₀ BJ hB).symm) := by
  apply respects_iff_of_equiv (properEquiv₀ BJ hB)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (cell_idx₀ (.inl (.inl d.1)))).symm
  · change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔
      ((enlarged₀).cell (old₀ d.1)).1 ⊆
      ((enlarged₀).cell (old₀ e.1)).1
    simp only [ cell_idx, GradeCutPairCarrier.idx]
  · exact (old_row₀ b.1 d).symm

include hmatch in
theorem lower_respects_iff (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ k)
    p :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows₀) BJ
        (p ∘ (belowEquiv₀ BJ hBJ).symm) := by
  apply respects_iff_of_equiv (belowEquiv₀ BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_index₀ d.1)).symm)
    (fun d e => ?_)
    (fun b d _ => (embedded_row hmatch b.1 d).symm) p
  change ((small₀).cell d.1).1 ⊆
      ((small₀).cell e.1).1 ↔
    ((enlarged₀).cell (embed₀ d.1)).1 ⊆
      ((enlarged₀).cell (embed₀ e.1)).1
  simp only [embed_index]

include hmatch in
theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows₀).IsConsistent := by
  have hold (c : Cell D) :
      RespectsSemanticsBelow (rows₀)
        ((enlarged₀).cell (old₀ c))
        ((rows₀).E (old₀ c)) := by
    have ht := (proper_respects_iff hp hjk sem low (D.cell c)
      (GradeCutLayerRows.proper_scope D hp c) _).mp (hs c)
    have hu := GradeCutLayerRows.cast_respects
      (cell_idx₀ (.inl (.inl c))).symm ht
    convert hu using 1
    funext d
    let e := ownerEquiv₀ c
    let d' : (enlarged₀).below (D.cell c) :=
      ⟨d.1, by simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    have he  :=
      congrArg (fun z => z.1)
        (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans
      (old_row₀ c (e.symm d'))
  have hlow (c : Cell (small₀)) :
      RespectsSemanticsBelow (rows₀)
        ((enlarged₀).cell (embed₀ c))
        ((rows₀).E (embed₀ c)) := by
    have ht := (lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch _
      (small_grade₀ c) _).mp (hl c)
    have hu := GradeCutLayerRows.cast_respects (embed_index₀ c).symm ht
    convert hu using 1
    funext d
    let e := belowEquiv₀ _ (small_grade₀ c)
    let d' : (enlarged₀).below
        ((small₀).cell c) :=
      ⟨d.1, by simpa only [embed_index] using d.2⟩
    have he  :=
      congrArg (fun z => z.1) (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans
      (embedded_row hmatch c (e.symm d'))
  intro c
  obtain ⟨x, rfl⟩ := (occEquiv₀).surjective c
  rcases x with (d | q) | r
  · exact hold d
  · have h := hlow (cell₀ (.inl (.inr q)))
    exact (congrArg (fun a => RespectsSemanticsBelow
      (rows₀)
      ((enlarged₀).cell a)
      ((rows₀).E a))
      (embed_cell₀ (.inl (.inr q)))).mp h
  · have h := hlow (cell₀ (.inr r))
    exact (congrArg (fun a => RespectsSemanticsBelow
      (rows₀)
      ((enlarged₀).cell a)
      ((rows₀).E a))
      (embed_cell₀ (.inr r))).mp h

def glue (p : CellLabels D) (r : CellLabels (small₀))
    (d : Cell (enlarged₀)) :=
  match (occEquiv₀).symm d with
  | .inl (.inl a) => p a
  | .inl (.inr q) => r (cell₀ (.inl (.inr q)))
  | .inr q => r (cell₀ (.inr q))

local notation "glue₀" => glue D Q R j k hj hjA hk hkA

variable {D Q R j k hj hjA hk hkA} in
theorem glue_old p r
    d : glue₀ p r (old₀ d) = p d := by
  simp  [glue,  cell, ]

theorem glue_embed p r
    (hag : ∀ c, r (old₀₀ c) =
      p (GradeCutBoundary.toCell D k c)) d :
    glue₀ p r (embed₀ d) = r d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change glue₀ p r
    (embed₀ (cell _ _ _ _ _ _ _ _ _ x)) = _
  rw [embed_cell]
  rcases x with (d | q) | q
  · exact (glue_old p r _).trans (hag d).symm
  · simp_all [glue, cell]
  · simp_all [glue, cell]

include hmatch in
theorem glue_respects {p} {r}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (old₀₀ c) =
      p (GradeCutBoundary.toCell D k c)) :
    RespectsSemantics (rows₀)
      (glue₀ p r) := by
  apply GradeCutLayerRows.respects_of_lower
  intro c
  obtain ⟨x, rfl⟩ := (occEquiv₀).surjective c
  change RespectsSemanticsBelow _
    ((enlarged₀).cell (cell₀₀ x)) _
  have hlow (BJ : GradedIndex ι) (hBJ : BJ.2 ≤ k) :
      RespectsSemanticsBelow (rows₀) BJ
        (fun d => glue₀ p r d.1) := by
    have ht := (lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch BJ hBJ _).mp
      (hr.toBelow BJ)
    convert ht using 1
    funext d
    let e := belowEquiv₀ BJ hBJ
    exact (congrArg (glue₀ p r)
      (congrArg Subtype.val (e.apply_symm_apply d))).symm.trans
        (glue_embed D Q R j k hj hjA hk hkA p r hag _)
  rcases x with (a | q) | q
  · have ht := (proper_respects_iff hp hjk sem low (D.cell a)
      (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.toBelow (D.cell a))
    have hu := GradeCutLayerRows.cast_respects
      (cell_idx₀ (.inl (.inl a))).symm ht
    let e := ownerEquiv₀ a
    have heq : (fun d : (enlarged₀).below
        ((enlarged₀).cell (cell₀₀ (.inl (.inl a)))) =>
        glue₀ p r d.1) =
      (fun d => p (e.symm ⟨d.1, by
        simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩).1) := by
      funext d
      let d' : (enlarged₀).below (D.cell a) :=
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
      exact (congrArg (glue₀ p r)
        (congrArg Subtype.val (e.apply_symm_apply d'))).symm.trans
          (glue_old p r _)
    exact heq.symm ▸ hu
  · exact hlow _ (by rw [cell_idx]; exact hjk)
  · exact hlow _ (by rw [cell_idx]; exact le_rfl)

