/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalCoatomBountiful

@[expose] public section

namespace VaughtConjecture.Knight.GradeCutPairCarrier
open Transform Value ExtOrd SourceLayerCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)

abbrev lower := SourceLayerCarrier.scheme D Q j hj hjA
abbrev enlarged := SourceLayerCarrier.scheme (lower D Q j hj hjA) R k hk hkA
abbrev small := enlarged (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA

def occEquiv : ((Cell D ⊕ Q) ⊕ R) ≃ Cell (enlarged D Q R j k hj hjA hk hkA) :=
  (Equiv.sumCongr (enumeration D Q j hj hjA) (Equiv.refl R)).trans
    (enumeration (lower D Q j hj hjA) R k hk hkA)

def cell (x : (Cell D ⊕ Q) ⊕ R) := occEquiv D Q R j k hj hjA hk hkA x

def idx : (Cell D ⊕ Q) ⊕ R → Finset ι × ℕ
  | .inl (.inl d) => D.cell d
  | .inl (.inr _) => (A, j)
  | .inr _ => (A, k)

theorem cell_idx (x : (Cell D ⊕ Q) ⊕ R) :
    (enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x) =
      idx D Q R j k x := by
  rcases x with (d | q) | r
  · change (enlarged D Q R j k hj hjA hk hkA).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inl d)))) = D.cell d
    simp only [cell_toCell, index]
  · change (enlarged D Q R j k hj hjA hk hkA).cell
      (toCell _ R k hk hkA (.inl (toCell D Q j hj hjA (.inr q)))) = (A, j)
    simp only [cell_toCell, index]
  · exact cell_toCell _ R k hk hkA (.inr r)

abbrev old (d : Cell D) := cell D Q R j k hj hjA hk hkA (.inl (.inl d))

def embed (d : Cell (small D Q R j k hj hjA hk hkA)) :=
  cell D Q R j k hj hjA hk hkA
    (Sum.map (Sum.map (GradeCutBoundary.toCell D k) id) id
      ((occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).symm d))

theorem embed_cell (x : (Cell (GradeCutBoundary.scheme D k) ⊕ Q) ⊕ R) :
    embed D Q R j k hj hjA hk hkA
      (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA x) =
    cell D Q R j k hj hjA hk hkA (Sum.map (Sum.map (GradeCutBoundary.toCell D k) id) id x) := by
  simp only [embed, cell, Equiv.symm_apply_apply]

theorem embed_index (d : Cell (small D Q R j k hj hjA hk hkA)) :
    (enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA d) =
      (small D Q R j k hj hjA hk hkA).cell d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change (enlarged D Q R j k hj hjA hk hkA).cell
    (embed D Q R j k hj hjA hk hkA (cell _ _ _ _ _ _ _ _ _ x)) =
      (small D Q R j k hj hjA hk hkA).cell (cell _ _ _ _ _ _ _ _ _ x)
  rw [embed_cell, cell_idx, cell_idx]
  rcases x with (d | q) | r <;> rfl

theorem embed_injective : Function.Injective (embed D Q R j k hj hjA hk hkA) := by
  intro d e h
  apply (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).symm.injective
  exact (Sum.map_injective.mpr ⟨Sum.map_injective.mpr
    ⟨(GradeCutBoundary.toCell D k).injective, Function.injective_id⟩,
      Function.injective_id⟩) ((occEquiv D Q R j k hj hjA hk hkA).injective h)

theorem exhaustive (d : Cell (enlarged D Q R j k hj hjA hk hkA))
    (hd : (enlarged D Q R j k hj hjA hk hkA).grade d ≤ k) :
    ∃ c, embed D Q R j k hj hjA hk hkA c = d := by
  obtain ⟨x, rfl⟩ := (occEquiv D Q R j k hj hjA hk hkA).surjective d
  change (enlarged D Q R j k hj hjA hk hkA).grade (cell _ _ _ _ _ _ _ _ _ x) ≤ k at hd
  rw [CellScheme.grade, cell_idx] at hd
  rcases x with (d | q) | r
  · obtain ⟨c, hc⟩ := GradeCutBoundary.exhaustive D k hd
    refine ⟨cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inl c)), ?_⟩
    rw [embed_cell]
    change cell _ _ _ _ _ _ _ _ _ (.inl (.inl (GradeCutBoundary.toCell D k c))) = _
    rw [hc]; rfl
  · exact ⟨cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)),
      embed_cell D Q R j k hj hjA hk hkA _⟩
  · exact ⟨cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r),
      embed_cell D Q R j k hj hjA hk hkA _⟩

def belowEquiv (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) :
    (small D Q R j k hj hjA hk hkA).below BJ ≃
      (enlarged D Q R j k hj hjA hk hkA).below BJ :=
  Equiv.ofBijective (fun d => ⟨embed D Q R j k hj hjA hk hkA d.1, by
    simpa only [embed_index] using d.2⟩) ⟨by
      intro d e h
      exact Subtype.ext (embed_injective D Q R j k hj hjA hk hkA (congrArg Subtype.val h)), by
      intro d
      obtain ⟨c, hc⟩ := exhaustive D Q R j k hj hjA hk hkA d.1 (d.2.2.trans hBJ)
      refine ⟨⟨c, ?_⟩, Subtype.ext hc⟩
      simpa only [← embed_index D Q R j k hj hjA hk hkA c, hc] using d.2⟩

def properEquiv (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1) :
    D.below BJ ≃ (enlarged D Q R j k hj hjA hk hkA).below BJ :=
  (GradeCutLayerCarrier.properEquiv D Q j hj hjA BJ hB).trans
    (GradeCutLayerCarrier.properEquiv (lower D Q j hj hjA) R k hk hkA BJ hB)

theorem small_grade (hjk : j ≤ k) (d : Cell (small D Q R j k hj hjA hk hkA)) :
    (small D Q R j k hj hjA hk hkA).grade d ≤ k := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change (small D Q R j k hj hjA hk hkA).grade (cell _ _ _ _ _ _ _ _ _ x) ≤ k
  rw [CellScheme.grade, cell_idx]
  rcases x with (d | q) | r
  · exact GradeCutBoundary.grade_bound D k d
  · exact hjk
  · exact le_rfl

end
end VaughtConjecture.Knight.GradeCutPairCarrier

namespace VaughtConjecture.Knight.RecursiveSourceCarrier
open Transform Value ExtOrd
open scoped BigOperators
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : ℕ → Type*) [∀ j, Fintype (Q j)]

def scheme : (n : ℕ) → n ≤ A.card → CellScheme A
  | 0, _ => D
  | n + 1, hn => SourceLayerCarrier.scheme (scheme n (Nat.le_of_succ_le hn))
      (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn

def step (n : ℕ) (hn : n + 1 ≤ A.card) :
    Cell (scheme D Q n (Nat.le_of_succ_le hn)) ↪o Cell (scheme D Q (n + 1) hn) :=
  OrderEmbedding.ofStrictMono
    (fun d => SourceLayerCarrier.toCell (scheme D Q n (Nat.le_of_succ_le hn))
      (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn (.inl d))
    (SourceLayerCarrier.old_order _ _ _ _ _)

theorem step_cell (n : ℕ) (hn : n + 1 ≤ A.card)
    (d : Cell (scheme D Q n (Nat.le_of_succ_le hn))) :
    (scheme D Q (n + 1) hn).cell (step D Q n hn d) =
      (scheme D Q n (Nat.le_of_succ_le hn)).cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ (.inl d)

def embed (m : ℕ) (hm : m ≤ A.card) : (t : ℕ) → (h : m + t ≤ A.card) →
    Cell (scheme D Q m hm) ↪o Cell (scheme D Q (m + t) h)
  | 0, _ => OrderEmbedding.ofStrictMono id strictMono_id
  | t + 1, h => (embed m hm t (by omega)).trans (step D Q (m + t) h)

theorem embed_cell (m : ℕ) (hm : m ≤ A.card) (t : ℕ) (h : m + t ≤ A.card)
    (d : Cell (scheme D Q m hm)) :
    (scheme D Q (m + t) h).cell (embed D Q m hm t h d) = (scheme D Q m hm).cell d := by
  induction t with
  | zero => rfl
  | succ t ih => exact (step_cell D Q (m + t) h _).trans (ih (by omega))

def boundary : (n : ℕ) → (hn : n ≤ A.card) → Cell D ↪o Cell (scheme D Q n hn)
  | 0, _ => OrderEmbedding.ofStrictMono id strictMono_id
  | n + 1, hn => (boundary n (Nat.le_of_succ_le hn)).trans (step D Q n hn)

theorem boundary_cell (n : ℕ) (hn : n ≤ A.card) (d : Cell D) :
    (scheme D Q n hn).cell (boundary D Q n hn d) = D.cell d := by
  induction n with
  | zero => rfl
  | succ n ih => exact (step_cell D Q n hn _).trans (ih (Nat.le_of_succ_le hn))

abbrev controller (n : ℕ) (hn : n + 1 ≤ A.card) (q : Q (n + 1)) :=
  SourceLayerCarrier.controller (scheme D Q n (Nat.le_of_succ_le hn))
    (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn q

theorem controller_cell (n : ℕ) (hn : n + 1 ≤ A.card) (q : Q (n + 1)) :
    (scheme D Q (n + 1) hn).cell (controller D Q n hn q).1 = (A, n + 1) :=
  (controller D Q n hn q).2

/-- A controller remains a distinct actual occurrence at every later stage. -/
def retained (n t : ℕ) (h : n + 1 + t ≤ A.card) (q : Q (n + 1)) :
    Cell (scheme D Q (n + 1 + t) h) :=
  embed D Q (n + 1) (by omega) t h (controller D Q n (by omega) q).1

theorem retained_cell (n t : ℕ) (h : n + 1 + t ≤ A.card) (q : Q (n + 1)) :
    (scheme D Q (n + 1 + t) h).cell (retained D Q n t h q) = (A, n + 1) :=
  (embed_cell D Q (n + 1) (by omega) t h _).trans (controller_cell D Q n (by omega) q)

theorem classify (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme D Q n hn)) :
    (∃ c : Cell D, boundary D Q n hn c = d) ∨
      ∃ j, 0 < j ∧ j ≤ n ∧ (scheme D Q n hn).cell d = (A, j) := by
  induction n with
  | zero => exact Or.inl ⟨d, rfl⟩
  | succ n ih =>
    obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration
      (scheme D Q n (Nat.le_of_succ_le hn)) (Q (n + 1)) (n + 1) (Nat.succ_pos n) hn).surjective d
    cases x with
    | inl d =>
      rcases ih (Nat.le_of_succ_le hn) d with ⟨c, hc⟩ | ⟨j, hj, hjn, hd⟩
      · exact Or.inl ⟨c, congrArg (step D Q n hn) hc⟩
      · exact Or.inr ⟨j, hj, hjn.trans (Nat.le_succ n), (step_cell D Q n hn d).trans hd⟩
    | inr q => exact Or.inr ⟨n + 1, Nat.succ_pos n, le_rfl, controller_cell D Q n hn q⟩

theorem full_grade (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme D Q n hn))
    (hd : (scheme D Q n hn).scope d = A) : (scheme D Q n hn).grade d ≤ n := by
  rcases classify D Q n hn d with ⟨c, rfl⟩ | ⟨j, _, hj, he⟩
  · exact (hp c ((congrArg Prod.fst (boundary_cell D Q n hn c)).symm.trans hd)).elim
  · change ((scheme D Q n hn).cell d).2 ≤ n
    rw [he]
    exact hj

/-- Proper old owners may be higher than the next layer. Separation comes
from their scope, not an incorrect whole-predecessor grade bound. -/
theorem separated (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme D Q n hn)) :
    ¬ GradedLe (A, n + 1) ((scheme D Q n hn).cell d) := by
  intro h
  have hs : (scheme D Q n hn).scope d = A := Finset.Subset.antisymm
    ((scheme D Q n hn).isPlan.subset_of_mem ((scheme D Q n hn).scope_mem_plan d)) h.1
  exact (Nat.not_succ_le_self n) (h.2.trans (full_grade D Q hp n hn d hs))

end
end VaughtConjecture.Knight.RecursiveSourceCarrier

namespace VaughtConjecture.Knight.GradeCutPairRows
open Transform Value ExtOrd GradeCutPairCarrier
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q R : Type*) [Fintype Q] [Fintype R]
variable (j k : ℕ) (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j ≤ k)
variable (sem : Semantics D) (low : Semantics (small D Q R j k hj hjA hk hkA))

def ownerEquiv (c : Cell D) :=
  properEquiv D Q R j k hj hjA hk hkA (D.cell c) (GradeCutLayerRows.proper_scope D hp c)

def liftedRow (c : Cell (small D Q R j k hj hjA hk hkA)) :
    (enlarged D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c) → ExtOrd :=
  low.E c ∘ (belowEquiv D Q R j k hj hjA hk hkA _
    (small_grade D Q R j k hj hjA hk hkA hjk c)).symm

theorem liftedRow_orderly (c : Cell (small D Q R j k hj hjA hk hkA))
    (d : (enlarged D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c)) :
    SelfVis ((enlarged D Q R j k hj hjA hk hkA).grade d.1)
      (liftedRow D Q R j k hj hjA hk hkA hjk low c d) := by
  let e := belowEquiv D Q R j k hj hjA hk hkA _
    (small_grade D Q R j k hj hjA hk hkA hjk c)
  have he := congrArg Subtype.val (e.apply_symm_apply d)
  change embed D Q R j k hj hjA hk hkA (e.symm d).1 = d.1 at he
  have hg := congrArg Prod.snd (embed_index D Q R j k hj hjA hk hkA (e.symm d).1)
  rw [he] at hg
  change (enlarged D Q R j k hj hjA hk hkA).grade d.1 =
    (small D Q R j k hj hjA hk hkA).grade (e.symm d).1 at hg
  rw [hg]
  exact (low.orderly c (e.symm d)).symm

def rowAt (x : (Cell D ⊕ Q) ⊕ R) :
    (enlarged D Q R j k hj hjA hk hkA).below (idx D Q R j k x) → ExtOrd :=
  match x with
  | .inl (.inl c) => sem.E c ∘ (ownerEquiv D Q R j k hj hjA hk hkA hp c).symm
  | .inl (.inr q) => fun d =>
      liftedRow D Q R j k hj hjA hk hkA hjk low
        (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
  | .inr r => fun d =>
      liftedRow D Q R j k hj hjA hk hkA hjk low
        (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r))
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩

theorem rowAt_orderly (x : (Cell D ⊕ Q) ⊕ R)
    (d : (enlarged D Q R j k hj hjA hk hkA).below (idx D Q R j k x)) :
    SelfVis ((enlarged D Q R j k hj hjA hk hkA).grade d.1)
      (rowAt D Q R j k hj hjA hk hkA hp hjk sem low x d) := by
  rcases x with (c | q) | r
  · let e := ownerEquiv D Q R j k hj hjA hk hkA hp c
    have he := congrArg Subtype.val (e.apply_symm_apply d)
    change old D Q R j k hj hjA hk hkA (e.symm d).1 = d.1 at he
    have hg := congrArg Prod.snd (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl (e.symm d).1)))
    change (enlarged D Q R j k hj hjA hk hkA).grade
      (old D Q R j k hj hjA hk hkA (e.symm d).1) = D.grade (e.symm d).1 at hg
    rw [he] at hg
    rw [hg]
    exact (sem.orderly c (e.symm d)).symm
  · dsimp only [rowAt]
    exact liftedRow_orderly D Q R j k hj hjA hk hkA hjk low
      (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q))) _
  · dsimp only [rowAt]
    exact liftedRow_orderly D Q R j k hj hjA hk hkA hjk low
      (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r)) _

def rows : Semantics (enlarged D Q R j k hj hjA hk hkA) where
  E c d := rowAt D Q R j k hj hjA hk hkA hp hjk sem low
    ((occEquiv D Q R j k hj hjA hk hkA).symm c)
    ⟨d.1, by
      have he := cell_idx D Q R j k hj hjA hk hkA ((occEquiv D Q R j k hj hjA hk hkA).symm c)
      change (enlarged D Q R j k hj hjA hk hkA).cell
        ((occEquiv D Q R j k hj hjA hk hkA) ((occEquiv D Q R j k hj hjA hk hkA).symm c)) = _ at he
      rw [Equiv.apply_symm_apply] at he
      rw [← he]
      exact d.2⟩
  orderly c d := (rowAt_orderly D Q R j k hj hjA hk hkA hp hjk sem low _ _).symm

theorem rowAt_congr {x y : (Cell D ⊕ Q) ⊕ R} (hxy : x = y)
    {d : (enlarged D Q R j k hj hjA hk hkA).below (GradeCutPairCarrier.idx D Q R j k x)}
    {e : (enlarged D Q R j k hj hjA hk hkA).below (GradeCutPairCarrier.idx D Q R j k y)}
    (hde : d.1 = e.1) :
    rowAt D Q R j k hj hjA hk hkA hp hjk sem low x d =
      rowAt D Q R j k hj hjA hk hkA hp hjk sem low y e := by
  subst y
  rw [Subtype.ext hde]

theorem rows_cell (x : (Cell D ⊕ Q) ⊕ R)
    (d : (enlarged D Q R j k hj hjA hk hkA).below
      ((enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x))) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E (cell D Q R j k hj hjA hk hkA x) d =
      rowAt D Q R j k hj hjA hk hkA hp hjk sem low x
        ⟨d.1, by simpa only [cell_idx] using d.2⟩ :=
  rowAt_congr D Q R j k hj hjA hk hkA hp hjk sem low
    ((occEquiv D Q R j k hj hjA hk hkA).symm_apply_apply x) rfl

theorem old_row (c : Cell D) (d : D.below (D.cell c)) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E
      (old D Q R j k hj hjA hk hkA c)
      ⟨(ownerEquiv D Q R j k hj hjA hk hkA hp c d).1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using
          (ownerEquiv D Q R j k hj hjA hk hkA hp c d).2⟩ =
    sem.E c d := by
  exact (rows_cell D Q R j k hj hjA hk hkA hp hjk sem low (.inl (.inl c)) _).trans
    (congrArg (sem.E c) ((ownerEquiv D Q R j k hj hjA hk hkA hp c).symm_apply_apply d))

variable (hmatch : ∀ (c : Cell (GradeCutBoundary.scheme D k))
    (d : (GradeCutBoundary.scheme D k).below ((GradeCutBoundary.scheme D k).cell c)),
    low.E (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c)
      ⟨old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA d.1, by
        simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩ =
      (GradeCutBoundary.rows D k sem).E c d)

include hmatch in
theorem embedded_row (c : Cell (small D Q R j k hj hjA hk hkA))
    (d : (small D Q R j k hj hjA hk hkA).below
      ((small D Q R j k hj hjA hk hkA).cell c)) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).E (embed D Q R j k hj hjA hk hkA c)
      ⟨embed D Q R j k hj hjA hk hkA d.1, by simpa only [embed_index] using d.2⟩ = low.E c d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective c
  change (rows D Q R j k hj hjA hk hkA hp hjk sem low).E
    (embed D Q R j k hj hjA hk hkA (cell _ _ _ _ _ _ _ _ _ x)) _ = _
  have helper (a : Cell (small D Q R j k hj hjA hk hkA))
      (e : (small D Q R j k hj hjA hk hkA).below ((small D Q R j k hj hjA hk hkA).cell a)) :
      liftedRow D Q R j k hj hjA hk hkA hjk low a
        ⟨embed D Q R j k hj hjA hk hkA e.1, by simpa only [embed_index] using e.2⟩ = low.E a e :=
    congrArg (low.E a) ((belowEquiv D Q R j k hj hjA hk hkA _
      (small_grade D Q R j k hj hjA hk hkA hjk a)).symm_apply_apply e)
  rcases x with (c | q) | r
  · let ep := properEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA
      ((GradeCutBoundary.scheme D k).cell c)
      (GradeCutLayerRows.proper_scope D hp (GradeCutBoundary.toCell D k c))
    let d' : (small D Q R j k hj hjA hk hkA).below ((GradeCutBoundary.scheme D k).cell c) :=
      ⟨d.1, by
        have hd := d.2
        change GradedLe _ ((small D Q R j k hj hjA hk hkA).cell
          (cell _ _ _ _ _ _ _ _ _ (.inl (.inl c)))) at hd
        simpa only [cell_idx, GradeCutPairCarrier.idx] using hd⟩
    obtain ⟨e, he⟩ := ep.surjective d'
    have hev := congrArg Subtype.val he
    change old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA e.1 = d.1 at hev
    have hr := old_row D Q R j k hj hjA hk hkA hp hjk sem low
      (GradeCutBoundary.toCell D k c)
      (GradeCutBoundary.belowEquiv D k _ (GradeCutBoundary.grade_bound D k c) e)
    have hc := embed_cell D Q R j k hj hjA hk hkA (.inl (.inl c))
    refine (Semantics.E_congr' _ hc ?_).trans (hr.trans ?_)
    · exact (congrArg (embed D Q R j k hj hjA hk hkA) hev).symm.trans
        (embed_cell D Q R j k hj hjA hk hkA (.inl (.inl e.1)))
    · exact (hmatch c e).symm.trans (low.E_congr' rfl hev)
  · have hc := embed_cell D Q R j k hj hjA hk hkA (.inl (.inr q))
    refine (Semantics.E_congr' _ hc
      (d' := ⟨embed D Q R j k hj hjA hk hkA d.1, by
        rw [embed_index, cell_idx]
        have hd := d.2
        change GradedLe _ ((small D Q R j k hj hjA hk hkA).cell
          (cell _ _ _ _ _ _ _ _ _ (.inl (.inr q)))) at hd
        rw [cell_idx] at hd
        exact hd⟩) rfl).trans ?_
    exact (rows_cell D Q R j k hj hjA hk hkA hp hjk sem low (.inl (.inr q)) _).trans
      (helper _ d)
  · have hc := embed_cell D Q R j k hj hjA hk hkA (.inr r)
    refine (Semantics.E_congr' _ hc
      (d' := ⟨embed D Q R j k hj hjA hk hkA d.1, by
        rw [embed_index, cell_idx]
        have hd := d.2
        change GradedLe _ ((small D Q R j k hj hjA hk hkA).cell
          (cell _ _ _ _ _ _ _ _ _ (.inr r))) at hd
        rw [cell_idx] at hd
        exact hd⟩) rfl).trans ?_
    exact (rows_cell D Q R j k hj hjA hk hkA hp hjk sem low (.inr r) _).trans
      (helper _ d)

theorem proper_respects_iff (BJ : Finset ι × ℕ) (hB : ¬ A ⊆ BJ.1)
    (p : D.below BJ → ExtOrd) :
    RespectsSemanticsBelow sem BJ p ↔
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (p ∘ (properEquiv D Q R j k hj hjA hk hkA BJ hB).symm) := by
  apply respects_iff_of_equiv (properEquiv D Q R j k hj hjA hk hkA BJ hB)
    (fun d => ?_) (fun d e => ?_) (fun b d _ => ?_) p
  · exact (congrArg Prod.snd (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl d.1)))).symm
  · change (D.cell d.1).1 ⊆ (D.cell e.1).1 ↔
      ((enlarged D Q R j k hj hjA hk hkA).cell (old D Q R j k hj hjA hk hkA d.1)).1 ⊆
      ((enlarged D Q R j k hj hjA hk hkA).cell (old D Q R j k hj hjA hk hkA e.1)).1
    simp only [old, cell_idx, GradeCutPairCarrier.idx]
  · exact (old_row D Q R j k hj hjA hk hkA hp hjk sem low b.1 d).symm

include hmatch in
theorem lower_respects_iff (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k)
    (p : (small D Q R j k hj hjA hk hkA).below BJ → ExtOrd) :
    RespectsSemanticsBelow low BJ p ↔
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (p ∘ (belowEquiv D Q R j k hj hjA hk hkA BJ hBJ).symm) := by
  apply respects_iff_of_equiv (belowEquiv D Q R j k hj hjA hk hkA BJ hBJ)
    (fun d => (congrArg Prod.snd (embed_index D Q R j k hj hjA hk hkA d.1)).symm)
    (fun d e => ?_)
    (fun b d _ => (embedded_row D Q R j k hj hjA hk hkA hp hjk sem low hmatch b.1 d).symm) p
  change ((small D Q R j k hj hjA hk hkA).cell d.1).1 ⊆
      ((small D Q R j k hj hjA hk hkA).cell e.1).1 ↔
    ((enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA d.1)).1 ⊆
      ((enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA e.1)).1
  simp only [embed_index]

include hmatch in
theorem consistent (hs : sem.IsConsistent) (hl : low.IsConsistent) :
    (rows D Q R j k hj hjA hk hkA hp hjk sem low).IsConsistent := by
  have hold (c : Cell D) :
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low)
        ((enlarged D Q R j k hj hjA hk hkA).cell (old D Q R j k hj hjA hk hkA c))
        ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E (old D Q R j k hj hjA hk hkA c)) := by
    have ht := (proper_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low (D.cell c)
      (GradeCutLayerRows.proper_scope D hp c) _).mp (hs c)
    have hu := GradeCutLayerRows.cast_respects _ _
      (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl c))).symm ht
    convert hu using 1
    funext d
    let e := ownerEquiv D Q R j k hj hjA hk hkA hp c
    let d' : (enlarged D Q R j k hj hjA hk hkA).below (D.cell c) :=
      ⟨d.1, by simpa only [old, cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    have he : (e (e.symm d')).1 = d.1 :=
      congrArg (fun z : (enlarged D Q R j k hj hjA hk hkA).below (D.cell c) => z.1)
        (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans
      (old_row D Q R j k hj hjA hk hkA hp hjk sem low c (e.symm d'))
  have hlow (c : Cell (small D Q R j k hj hjA hk hkA)) :
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low)
        ((enlarged D Q R j k hj hjA hk hkA).cell (embed D Q R j k hj hjA hk hkA c))
        ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E (embed D Q R j k hj hjA hk hkA c)) := by
    have ht := (lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch _
      (small_grade D Q R j k hj hjA hk hkA hjk c) _).mp (hl c)
    have hu := GradeCutLayerRows.cast_respects _ _ (embed_index D Q R j k hj hjA hk hkA c).symm ht
    convert hu using 1
    funext d
    let e := belowEquiv D Q R j k hj hjA hk hkA _ (small_grade D Q R j k hj hjA hk hkA hjk c)
    let d' : (enlarged D Q R j k hj hjA hk hkA).below
        ((small D Q R j k hj hjA hk hkA).cell c) :=
      ⟨d.1, by simpa only [embed_index] using d.2⟩
    have he : (e (e.symm d')).1 = d.1 :=
      congrArg (fun z : (enlarged D Q R j k hj hjA hk hkA).below
        ((small D Q R j k hj hjA hk hkA).cell c) => z.1) (e.apply_symm_apply d')
    exact (Semantics.E_congr' _ rfl he).symm.trans
      (embedded_row D Q R j k hj hjA hk hkA hp hjk sem low hmatch c (e.symm d'))
  intro c
  obtain ⟨x, rfl⟩ := (occEquiv D Q R j k hj hjA hk hkA).surjective c
  rcases x with (d | q) | r
  · exact hold d
  · have h := hlow (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))
    exact (congrArg (fun a => RespectsSemanticsBelow
      (rows D Q R j k hj hjA hk hkA hp hjk sem low)
      ((enlarged D Q R j k hj hjA hk hkA).cell a)
      ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E a))
      (embed_cell D Q R j k hj hjA hk hkA (.inl (.inr q)))).mp h
  · have h := hlow (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr r))
    exact (congrArg (fun a => RespectsSemanticsBelow
      (rows D Q R j k hj hjA hk hkA hp hjk sem low)
      ((enlarged D Q R j k hj hjA hk hkA).cell a)
      ((rows D Q R j k hj hjA hk hkA hp hjk sem low).E a))
      (embed_cell D Q R j k hj hjA hk hkA (.inr r))).mp h

def glue (p : Cell D → ExtOrd) (r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd)
    (d : Cell (enlarged D Q R j k hj hjA hk hkA)) : ExtOrd :=
  match (occEquiv D Q R j k hj hjA hk hkA).symm d with
  | .inl (.inl a) => p a
  | .inl (.inr q) => r (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inl (.inr q)))
  | .inr q => r (cell (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA (.inr q))

theorem glue_old (p : Cell D → ExtOrd) (r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd)
    (d : Cell D) : glue D Q R j k hj hjA hk hkA p r (old D Q R j k hj hjA hk hkA d) = p d := by
  simp only [glue, old, cell, Equiv.symm_apply_apply]

theorem glue_embed (p : Cell D → ExtOrd) (r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd)
    (hag : ∀ c, r (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c) =
      p (GradeCutBoundary.toCell D k c)) (d : Cell (small D Q R j k hj hjA hk hkA)) :
    glue D Q R j k hj hjA hk hkA p r (embed D Q R j k hj hjA hk hkA d) = r d := by
  obtain ⟨x, rfl⟩ := (occEquiv (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA).surjective d
  change glue D Q R j k hj hjA hk hkA p r
    (embed D Q R j k hj hjA hk hkA (cell _ _ _ _ _ _ _ _ _ x)) = _
  rw [embed_cell]
  rcases x with (d | q) | q
  · exact (glue_old D Q R j k hj hjA hk hkA p r _).trans (hag d).symm
  · simp only [Sum.map_inl, Sum.map_inr, id_eq, glue, cell, Equiv.symm_apply_apply]
  · simp only [Sum.map_inr, id_eq, glue, cell, Equiv.symm_apply_apply]

include hmatch in
theorem glue_respects {p : Cell D → ExtOrd} {r : Cell (small D Q R j k hj hjA hk hkA) → ExtOrd}
    (hpr : RespectsSemantics sem p) (hr : RespectsSemantics low r)
    (hag : ∀ c, r (old (GradeCutBoundary.scheme D k) Q R j k hj hjA hk hkA c) =
      p (GradeCutBoundary.toCell D k c)) :
    RespectsSemantics (rows D Q R j k hj hjA hk hkA hp hjk sem low)
      (glue D Q R j k hj hjA hk hkA p r) := by
  apply GradeCutLayerRows.respects_of_lower
  intro c
  obtain ⟨x, rfl⟩ := (occEquiv D Q R j k hj hjA hk hkA).surjective c
  change RespectsSemanticsBelow _
    ((enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA x)) _
  have hlow (BJ : Finset ι × ℕ) (hBJ : BJ.2 ≤ k) :
      RespectsSemanticsBelow (rows D Q R j k hj hjA hk hkA hp hjk sem low) BJ
        (fun d => glue D Q R j k hj hjA hk hkA p r d.1) := by
    have ht := (lower_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low hmatch BJ hBJ _).mp
      (hr.toBelow BJ)
    convert ht using 1
    funext d
    let e := belowEquiv D Q R j k hj hjA hk hkA BJ hBJ
    exact (congrArg (glue D Q R j k hj hjA hk hkA p r)
      (congrArg Subtype.val (e.apply_symm_apply d))).symm.trans
        (glue_embed D Q R j k hj hjA hk hkA p r hag _)
  rcases x with (a | q) | q
  · have ht := (proper_respects_iff D Q R j k hj hjA hk hkA hp hjk sem low (D.cell a)
      (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.toBelow (D.cell a))
    have hu := GradeCutLayerRows.cast_respects _ _
      (cell_idx D Q R j k hj hjA hk hkA (.inl (.inl a))).symm ht
    let e := ownerEquiv D Q R j k hj hjA hk hkA hp a
    have heq : (fun d : (enlarged D Q R j k hj hjA hk hkA).below
        ((enlarged D Q R j k hj hjA hk hkA).cell (cell D Q R j k hj hjA hk hkA (.inl (.inl a)))) =>
        glue D Q R j k hj hjA hk hkA p r d.1) =
      (fun d => p (e.symm ⟨d.1, by
        simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩).1) := by
      funext d
      let d' : (enlarged D Q R j k hj hjA hk hkA).below (D.cell a) :=
        ⟨d.1, by simpa only [cell_idx, GradeCutPairCarrier.idx] using d.2⟩
      exact (congrArg (glue D Q R j k hj hjA hk hkA p r)
        (congrArg Subtype.val (e.apply_symm_apply d'))).symm.trans
          (glue_old D Q R j k hj hjA hk hkA p r _)
    exact heq.symm ▸ hu
  · exact hlow _ (by rw [cell_idx]; exact hjk)
  · exact hlow _ (by rw [cell_idx]; exact le_rfl)

end
end VaughtConjecture.Knight.GradeCutPairRows

namespace VaughtConjecture.Knight.CanonicalPairBoundary
open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SourcePrefixRows
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j k : ℕ)
variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

abbrev boundary := GradeCutBoundary.scheme D k
abbrev boundaryRows := GradeCutBoundary.rows D k sem
abbrev firstProfiles := CanonicalGradeCutSections.Profiles (boundaryRows sem k) j
abbrev secondProfiles :=
  CanonicalFieldLayer.Profile (boundaryRows sem k) k (Cell (boundary (D := D) k)) id
abbrev lower := CanonicalMixedGradeLayers.scheme (boundaryRows sem k) j hj hjA k hk hkA
abbrev lowerRows := CanonicalMixedGradeLayers.rows (boundaryRows sem k) j hj hjA
  (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
abbrev scheme := GradeCutPairCarrier.enlarged D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev old := GradeCutPairCarrier.old D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev embed := GradeCutPairCarrier.embed D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA
abbrev rows := GradeCutPairRows.rows D (firstProfiles sem j k) (secondProfiles sem k)
  j k hj hjA hk hkA hp hjk.le sem (lowerRows sem j k hj hjA hk hkA hp hjk)

theorem overlap (c : Cell (boundary (D := D) k))
    (d : (boundary (D := D) k).below ((boundary (D := D) k).cell c)) :
    (lowerRows sem j k hj hjA hk hkA hp hjk).E
      (GradeCutPairCarrier.old (boundary (D := D) k) (firstProfiles sem j k)
        (secondProfiles sem k) j k hj hjA hk hkA c)
      ⟨GradeCutPairCarrier.old (boundary (D := D) k) (firstProfiles sem j k)
        (secondProfiles sem k) j k hj hjA hk hkA d.1, by
          simpa only [GradeCutPairCarrier.old, GradeCutPairCarrier.cell_idx,
            GradeCutPairCarrier.idx] using d.2⟩ = (boundaryRows sem k).E c d :=
  CanonicalMixedGradeLayers.original_row (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk c d

theorem consistent (hs : sem.IsConsistent) : (rows sem j k hj hjA hk hkA hp hjk).IsConsistent :=
  GradeCutPairRows.consistent D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) hs
    (CanonicalMixedGradeLayers.consistent (boundaryRows sem k) j hj hjA
      (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
      (GradeCutBoundary.consistent D k sem hs))

theorem lower_row (c : Cell (lower sem j k hj hjA hk hkA))
    (d : (lower sem j k hj hjA hk hkA).below ((lower sem j k hj hjA hk hkA).cell c)) :
    (rows sem j k hj hjA hk hkA hp hjk).E (embed sem j k hj hjA hk hkA c)
      ⟨embed sem j k hj hjA hk hkA d.1, by
        simpa only [embed, GradeCutPairCarrier.embed_index] using d.2⟩ =
      (lowerRows sem j k hj hjA hk hkA hp hjk).E c d :=
  GradeCutPairRows.embedded_row D _ _ j k hj hjA hk hkA hp hjk.le sem _
    (overlap sem j k hj hjA hk hkA hp hjk) c d

variable {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)

variable {G : Finset ExtOrd} {C : ExtOrd}

/-- Ordinary whole-boundary sections also allow literal top, independently
of the proper-profile selected operator. There is no ambient-cap conclusion. -/
theorem exists_whole {p : Cell D → ExtOrd} (hpr : RespectsSemantics sem p) :
    ∃ r : Cell (scheme sem j k hj hjA hk hkA) → ExtOrd,
      RespectsSemantics (rows sem j k hj hjA hk hkA hp hjk) r ∧
      ∀ d, r (old sem j k hj hjA hk hkA d) = p d := by
  obtain ⟨u, hu, hread⟩ := CanonicalSections.exists_whole (boundaryRows sem k) j hj hjA
    (GradeCutBoundary.proper D k hp) k (GradeCutBoundary.grade_bound D k) hk hkA hjk
    (GradeCutBoundary.restrict_respects D k sem hpr)
  let all (d : Cell (lower sem j k hj hjA hk hkA)) :
      (lower sem j k hj hjA hk hkA).below (A, k) :=
    ⟨d, (lower sem j k hj hjA hk hkA).isPlan.subset_of_mem
        ((lower sem j k hj hjA hk hkA).scope_mem_plan d),
      GradeCutPairCarrier.small_grade D _ _ j k hj hjA hk hkA hjk.le d⟩
  let v := fun d => u (all d)
  have hv : RespectsSemantics (lowerRows sem j k hj hjA hk hkA hp hjk) v :=
    hu.toRespects (fun d => (all d).2)
  refine ⟨GradeCutPairRows.glue D _ _ j k hj hjA hk hkA p v,
    GradeCutPairRows.glue_respects D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) hpr hv ?_,
    GradeCutPairRows.glue_old D _ _ j k hj hjA hk hkA p v⟩
  exact hread

end
end VaughtConjecture.Knight.CanonicalPairBoundary

namespace VaughtConjecture.Knight.CanonicalPairLocalSections
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalPairBoundary
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 2 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev one_le := (by decide : 1 ≤ 2).trans hA
abbrev carrier := scheme sem 1 2 (by decide) (one_le hA) (by decide) hA
abbrev semantics := rows sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)
abbrev original := old sem 1 2 (by decide) (one_le hA) (by decide) hA
abbrev small := lower sem 1 2 (by decide) (one_le hA) (by decide) hA
abbrev smallRows := lowerRows sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)

variable {K : ℕ} (hK : 2 ≤ K) {p : Cell D → ExtOrd}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

include hK hpr in
theorem cut_lawful : RespectsSemantics (GradeCutBoundary.rows D 2 sem)
    (fun d => p (GradeCutBoundary.toCell D 2 d)) := by
  have hr := GradeCutBoundary.pullback_respects D 2 sem le_rfl
    (hpr.mono (show GradedLe (A, 2) (A, K) from ⟨Finset.Subset.refl _, hK⟩))
  exact hr.toRespects (fun d =>
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D 2 d⟩)

def smallSection (G : Finset ExtOrd) (C : ExtOrd) : Cell (small sem hA) → ExtOrd :=
  CanonicalMixedGradeLayers.sectionOf (GradeCutBoundary.rows D 2 sem) 1 (by decide)
    (one_le hA) (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) hA (by decide) (cut_lawful sem hK hpr)
    (fun d => ht (GradeCutBoundary.toCell D 2 d)) G C

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) : Cell (carrier sem hA) → ExtOrd :=
  GradeCutPairRows.glue D _ _ 1 2 (by decide) (one_le hA) (by decide) hA p
    (smallSection sem hA hp hK hpr ht G C)

theorem section_old {G : Finset ExtOrd} {C : ExtOrd} (d : Cell D) :
    sectionOf sem hA hp hK hpr ht G C (original sem hA d) = p d :=
  GradeCutPairRows.glue_old D _ _ 1 2 (by decide) (one_le hA) (by decide) hA p _ d

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem small_readback (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (d : Cell (GradeCutBoundary.scheme D 2)) :
    smallSection sem hA hp hK hpr ht G C
      (GradeCutPairCarrier.old (GradeCutBoundary.scheme D 2) _ _ 1 2
        (by decide) (one_le hA) (by decide) hA d) = p (GradeCutBoundary.toCell D 2 d) :=
  CanonicalMixedGradeLayers.section_boundary (GradeCutBoundary.rows D 2 sem) 1 (by decide)
    (one_le hA) (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) hA (by decide) (cut_lawful sem hK hpr) _ hG hC d

theorem section_embedded (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (d : Cell (small sem hA)) :
    sectionOf sem hA hp hK hpr ht G C
      (embed sem 1 2 (by decide) (one_le hA) (by decide) hA d) =
      smallSection sem hA hp hK hpr ht G C d :=
  GradeCutPairRows.glue_embed D _ _ 1 2 (by decide) (one_le hA) (by decide) hA p _
    (small_readback sem hA hp hK hpr ht hG hC) d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C) :
    RespectsSemanticsBelow (semantics sem hA hp) (A, K)
      (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  obtain ⟨x, hx⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).surjective c.1
  have hc := c.2
  rw [← hx] at hc ⊢
  change RespectsSemanticsBelow (semantics sem hA hp)
    ((carrier sem hA).cell (GradeCutPairCarrier.cell D _ _ 1 2
      (by decide) (one_le hA) (by decide) hA x))
    (fun d => sectionOf sem hA hp hK hpr ht G C d.1)
  have hlow (J : Finset ι × ℕ) (hJ : J.2 ≤ 2) :
      RespectsSemanticsBelow (semantics sem hA hp) J
        (fun d => sectionOf sem hA hp hK hpr ht G C d.1) := by
    have hr := CanonicalMixedGradeLayers.section_lawful (GradeCutBoundary.rows D 2 sem)
      1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
      (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide)
      (cut_lawful sem hK hpr) (fun d => ht (GradeCutBoundary.toCell D 2 d)) hG hC
    have hs := (GradeCutPairRows.lower_respects_iff D _ _ 1 2 (by decide)
      (one_le hA) (by decide) hA hp (by decide) sem (smallRows sem hA hp)
      (overlap sem 1 2 (by decide) (one_le hA) (by decide) hA hp (by decide)) J hJ _).mp
      (hr.toBelow J)
    convert hs using 1
    funext d
    let e := GradeCutPairCarrier.belowEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
      1 2 (by decide) (one_le hA) (by decide) hA J hJ
    exact (congrArg (sectionOf sem hA hp hK hpr ht G C)
      (congrArg Subtype.val (e.apply_symm_apply d))).symm.trans
      (section_embedded sem hA hp hK hpr ht hG hC _)
  rcases x with (a | q) | q
  · have ha : GradedLe (D.cell a) (A, K) := by
      change GradedLe ((carrier sem hA).cell (GradeCutPairCarrier.cell D _ _ 1 2
        (by decide) (one_le hA) (by decide) hA (.inl (.inl a)))) (A, K) at hc
      simpa only [GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx] using hc
    let e := GradeCutPairRows.ownerEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
      1 2 (by decide)
      (one_le hA) (by decide) hA hp a
    have hr := (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide)
      (one_le hA) (by decide) hA hp (by decide) sem (smallRows sem hA hp)
      (D.cell a) (GradeCutLayerRows.proper_scope D hp a) _).mp (hpr.mono ha)
    have hs := GradeCutLayerRows.cast_respects _ _
      (GradeCutPairCarrier.cell_idx D (firstProfiles sem 1 2) (secondProfiles sem 2)
        1 2 (by decide) (one_le hA)
        (by decide) hA (.inl (.inl a))).symm hr
    change RespectsSemanticsBelow (semantics sem hA hp) _ _ at hs
    convert hs using 1
    funext d
    let d' : (carrier sem hA).below (D.cell a) := ⟨d.1, by
      simpa only [GradeCutPairCarrier.cell_idx, GradeCutPairCarrier.idx] using d.2⟩
    exact (congrArg (sectionOf sem hA hp hK hpr ht G C)
      (congrArg Subtype.val (e.apply_symm_apply d'))).symm.trans
      (section_old sem hA hp hK hpr ht (e.symm d').1)
  · exact hlow _ (by rw [GradeCutPairCarrier.cell_idx]; exact (by decide : 1 ≤ 2))
  · exact hlow _ (by rw [GradeCutPairCarrier.cell_idx]; exact le_rfl)

theorem section_bound (hC : SelfVis 2 C) (hb : ∀ d, p d ≤ C)
    (d : Cell (carrier sem hA)) : sectionOf sem hA hp hK hpr ht G C d ≤ C := by
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).symm d with (a | q) | q
  · exact hb a
  all_goals
    exact CanonicalMixedGradeLayers.section_bound (GradeCutBoundary.rows D 2 sem)
      1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
      (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide)
      (cut_lawful sem hK hpr) _ hC (fun a => hb (GradeCutBoundary.toCell D 2 a)) _

theorem section_supported {L : ℕ} (hL : 2 ≤ L) (hCG : C ∈ G)
    (d : Cell (carrier sem hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem hA hp hK hpr ht G C d) := by
  have hl (a : Cell (small sem hA)) : OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (smallSection sem hA hp hK hpr ht G C a) := by
    rcases CanonicalMixedGradeLayers.section_supported (GradeCutBoundary.rows D 2 sem)
      1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
      (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide) hL hCG
      (cut_lawful sem hK hpr) (fun d => ht (GradeCutBoundary.toCell D 2 d)) a with
      hb | hm | ⟨e, i, hi, he⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr ⟨GradeCutBoundary.toCell D 2 e, i, hi, he⟩)
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).symm d with (a | q) | q
  · change OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (p a)
    rcases ExtOrd.cases (p a) with hb | ht | ⟨v, hv⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inr ⟨a, L, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
    · by_cases hi : finitePart v < L
      · exact Or.inr (Or.inr ⟨a, finitePart v, hi.le, by
          rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
      · exact Or.inr (Or.inr ⟨a, L, le_rfl, by
          rw [hv, extVisibilityReplace_of_le_finitePart (not_lt.mp hi)]⟩)
  · exact hl _
  · exact hl _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis 2 z) (hC : SelfVis 2 C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem hA hp hK hpr ht G C) (sectionOf sem hA hp hK hqr htq G C) h := by
  have hl := CanonicalMixedGradeLayers.section_agreement (GradeCutBoundary.rows D 2 sem)
    1 (by decide) (one_le hA) (GradeCutBoundary.proper D 2 hp) 2
    (GradeCutBoundary.grade_bound D 2) (by decide) hA (by decide)
    (cut_lawful sem hK hpr) (cut_lawful sem hK hqr)
    (fun d => ht (GradeCutBoundary.toCell D 2 d))
    (fun d => htq (GradeCutBoundary.toCell D 2 d)) hG hC hh hhC
    (fun d => hag (GradeCutBoundary.toCell D 2 d))
  intro d
  unfold sectionOf GradeCutPairRows.glue
  rcases (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA).symm d with (a | r) | r
  · exact hag a
  · exact hl _
  · exact hl _

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell (carrier sem hA) → ExtOrd} (hread : ∀ d, r (original sem hA d) = p d) :
    RespectsSemanticsBelow (semantics sem hA hp) J (fun d => r d.1) := by
  let e := GradeCutPairCarrier.properEquiv D (firstProfiles sem 1 2) (secondProfiles sem 2)
    1 2 (by decide) (one_le hA) (by decide) hA J hJ
  have he : (fun d : (carrier sem hA).below J => r d.1) =
      (fun d : D.below J => p d.1) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hread a.1
  rw [he]
  exact (GradeCutPairRows.proper_respects_iff D _ _ 1 2 (by decide) (one_le hA)
    (by decide) hA hp (by decide) sem (smallRows sem hA hp) J hJ _).mp hpr

theorem full_short (c : Cell (carrier sem hA)) (hc : (carrier sem hA).scope c = A)
    (d : (carrier sem hA).below ((carrier sem hA).cell c)) :
    SharpWitnessComposition.Short ((carrier sem hA).grade c) ((semantics sem hA hp).E c d) := by
  have hc2 : (carrier sem hA).grade c ≤ 2 := by
    obtain ⟨x, rfl⟩ := (GradeCutPairCarrier.occEquiv D _ _ 1 2 (by decide)
      (one_le hA) (by decide) hA).surjective c
    change (carrier sem hA).grade (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x) ≤ 2
    change ((carrier sem hA).cell
      (GradeCutPairCarrier.cell _ _ _ _ _ _ _ _ _ x)).1 = A at hc
    rw [GradeCutPairCarrier.cell_idx] at hc
    rw [CellScheme.grade, GradeCutPairCarrier.cell_idx]
    rcases x with (c | q) | q
    · exact (hp c hc).elim
    · exact (by decide : 1 ≤ 2)
    · exact le_rfl
  obtain ⟨a, rfl⟩ := GradeCutPairCarrier.exhaustive D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA c hc2
  obtain ⟨e, rfl⟩ := (GradeCutPairCarrier.belowEquiv D _ _ 1 2 (by decide)
    (one_le hA) (by decide) hA _ hc2).surjective d
  have he := CanonicalPairBoundary.lower_row sem 1 2 (by decide) (one_le hA)
    (by decide) hA hp (by decide) a
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  have hv := CanonicalMixedGradeLayers.full_source_short
    (CanonicalPairBoundary.boundaryRows sem 2) 1 (by decide) (one_le hA)
    (GradeCutBoundary.proper D 2 hp) 2 (GradeCutBoundary.grade_bound D 2)
    (by decide) hA (by decide) a
    (by simpa only [CellScheme.scope, GradeCutPairCarrier.embed_index] using hc)
    ⟨e.1, by simpa only [GradeCutPairCarrier.embed_index] using e.2⟩
  rw [← he] at hv
  exact (congrArg (fun i => SharpWitnessComposition.Short i _) (congrArg Prod.snd
    (GradeCutPairCarrier.embed_index D _ _ 1 2 (by decide) (one_le hA)
      (by decide) hA a))).mpr hv

end
end VaughtConjecture.Knight.CanonicalPairLocalSections

namespace VaughtConjecture.Knight.CanonicalPairLowerLifting
open Transform Value ExtOrd CanonicalPairBoundary CoatomBoundaryExtension AmalgamationPlan
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j k : ℕ)
variable (hj : 0 < j) (hjA : j ≤ A.card) (hk : 0 < k) (hkA : k ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A) (hjk : j < k)

theorem transport_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ k)
    (hl : CappedLift (lowerRows sem j k hj hjA hk hkA hp hjk) h) :
    CappedLift (rows sem j k hj hjA hk hkA hp hjk) h := by
  let eI := GradeCutPairCarrier.belowEquiv D (firstProfiles sem j k) (secondProfiles sem k)
    j k hj hjA hk hkA I (h.2.trans hJ)
  let eJ := GradeCutPairCarrier.belowEquiv D (firstProfiles sem j k) (secondProfiles sem k)
    j k hj hjA hk hkA J hJ
  have respect (B : Finset ι × ℕ) (hB : B.2 ≤ k)
      (q : (scheme sem j k hj hjA hk hkA).below B → ExtOrd)
      (hq : RespectsSemanticsBelow (rows sem j k hj hjA hk hkA hp hjk) B q) :
      RespectsSemanticsBelow (lowerRows sem j k hj hjA hk hkA hp hjk) B
        (q ∘ GradeCutPairCarrier.belowEquiv D _ _ j k hj hjA hk hkA B hB) := by
    apply (GradeCutPairRows.lower_respects_iff D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) B hB _).mpr
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using hq
  have hm (d : (lower sem j k hj hjA hk hkA).below I) :
      eJ (CellScheme.below.mono h d) = CellScheme.below.mono h (eI d) := rfl
  intro p q γ hpr hqr hγ hag
  obtain ⟨r, hr, hcap, hread⟩ := hl (p ∘ eI) (q ∘ eJ) γ
    (respect I (h.2.trans hJ) p hpr) (respect J hJ q hqr) hγ (fun d => hag (eI d))
  refine ⟨r ∘ eJ.symm,
    (GradeCutPairRows.lower_respects_iff D _ _ j k hj hjA hk hkA hp hjk.le sem _
      (overlap sem j k hj hjA hk hkA hp hjk) J hJ r).mp hr,
    fun d => ?_, fun d => ?_⟩
  · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (eJ.symm d)
  · have he : eJ.symm (CellScheme.below.mono h d) = CellScheme.below.mono h (eI.symm d) := by
      apply eJ.injective
      rw [Equiv.apply_symm_apply, hm, Equiv.apply_symm_apply]
    rw [Function.comp_apply, he, hread]
    exact congrArg p (eI.apply_symm_apply d)

include hk in
/-- Grade restriction obtains its proper-target clauses from the old schemes.
Nominal indices above the cut are handled at the effective grade, without
changing the external cap. -/
theorem cut_oldLifts (hold : CanonicalCoatomBountiful.OldLifts sem) :
    CanonicalCoatomBountiful.OldLifts (boundaryRows sem k) := by
  intro I J hI hJ hJA h
  apply EffectiveGradeLifting.lift (GradeCutBoundary.grade_bound D k) h
  apply CanonicalLowerLift.cut_lift (EffectiveGradeLifting.cut_le h) (min_le_right _ _)
  have mem (B : Finset ι × ℕ) (hB : B ∈ Plan.gradedPlan D.plan) :
      EffectiveGradeLifting.cut (K := k) B ∈ Plan.gradedPlan D.plan := by
    obtain ⟨hs, hi, hc⟩ := Plan.mem_gradedPlan.mp hB
    exact Plan.mem_gradedPlan.mpr ⟨hs, lt_min hi hk, (min_le_left _ _).trans hc⟩
  exact hold _ _ (mem I hI) (mem J hJ) hJA (EffectiveGradeLifting.cut_le h)

variable (hA : 2 ≤ A.card) (hold : CanonicalCoatomBountiful.OldLifts sem)
variable {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
variable (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
  ∃ d : Cell D, D.cell d = (C, i))

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- Bountifulness of the actual grade-one/two lower carrier is constructed
from the two old schemes' clauses even when their proper owners have grade three
or higher. All original occurrences through grade two are retained. -/
theorem lower_bountiful :
    (lowerRows sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
      (by decide) hA hp (by decide)).IsBountiful := by
  apply CanonicalCoatomBountiful.bountiful (boundaryRows sem 2) hA
    (GradeCutBoundary.proper D 2 hp) (GradeCutBoundary.grade_bound D 2)
    (cut_oldLifts sem 2 (by decide) hold) hL hR hLA hRA hLc hRc hO hcover
  intro C hC hCA i hi hiC hi2
  obtain ⟨d, hd⟩ := hcomplete C hC hCA i hi hiC hi2
  have hg : D.grade d ≤ 2 := by change (D.cell d).2 ≤ 2; rw [hd]; exact hi2
  refine ⟨GradeCutBoundary.fromCell D 2 d hg, ?_⟩
  exact (congrArg D.cell (GradeCutBoundary.to_from D 2 d hg)).trans hd

include hold hL hR hLA hRA hLc hRc hO hcover hcomplete in
/-- One arbitrary lawful prescribed face, one arbitrary lawful lower ambient,
and the original permitted cap. The conclusion preserves the entire auxiliary
vector through grade two; no conditions on a future grade-three row are inputs. -/
theorem lower_lift {I J : Finset ι × ℕ}
    (hI : I ∈ Plan.gradedPlan D.plan) (hJ : J ∈ Plan.gradedPlan D.plan)
    (h : GradedLe I J) (hJ2 : J.2 ≤ 2) :
    CappedLift (rows sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
      (by decide) hA hp (by decide)) h := by
  apply transport_lift sem 1 2 (by decide) ((by decide : 1 ≤ 2).trans hA)
    (by decide) hA hp (by decide) h hJ2
  have hb := lower_bountiful sem hp hA hold hL hR hLA hRA hLc hRc hO hcover hcomplete
  by_cases he : I = J
  · subst J; exact lift_refl
  · exact hb I J hI hJ h he

end
end VaughtConjecture.Knight.CanonicalPairLowerLifting

namespace VaughtConjecture.Knight.CanonicalRecursiveInventory
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D)

abbrev UpperProfile (j : ℕ) := CanonicalFieldLayer.Profile (GradeCutBoundary.rows D j sem)
  j (Cell D) (GradeCutBoundary.toCell D j)

def Profile : ℕ → Type 1
  | 0 => PUnit
  | 1 => CanonicalPairBoundary.firstProfiles sem 1 2
  | 2 => CanonicalPairBoundary.secondProfiles sem 2
  | n + 3 => UpperProfile sem (n + 3)

instance (j : ℕ) : Fintype (Profile sem j) := by
  rcases j with _ | _ | _ | j <;> dsimp only [Profile] <;> infer_instance

abbrev scheme (n : ℕ) (hn : n ≤ A.card) := RecursiveSourceCarrier.scheme D (Profile sem) n hn
abbrev boundary (n : ℕ) (hn : n ≤ A.card) :=
  RecursiveSourceCarrier.boundary D (Profile sem) n hn

theorem boundary_cell (n : ℕ) (hn : n ≤ A.card) (d : Cell D) :
    (scheme sem n hn).cell (boundary sem n hn d) = D.cell d :=
  RecursiveSourceCarrier.boundary_cell D (Profile sem) n hn d

/-- Normalize from the actual current old lower domain; future fields are
retained in the vector but are not required to be lawful at absent owners. -/
def encode (n : ℕ) {p : Cell D → ExtOrd}
    (hp : RespectsSemanticsBelow sem (A, n + 3) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤) :
    Profile sem (n + 3) := by
  let j := n + 3
  have hr := GradeCutBoundary.pullback_respects D j sem le_rfl hp
  apply CanonicalFieldLayer.encode (GradeCutBoundary.rows D j sem) j (Cell D)
    (GradeCutBoundary.toCell D j) (GradeCutBoundary.grade_bound D j) _ ht
  exact hr.toRespects (fun d =>
    ⟨D.isPlan.subset_of_mem (D.scope_mem_plan _), GradeCutBoundary.grade_bound D j d⟩)

theorem separated (hp : ∀ d : Cell D, D.scope d ≠ A)
    (n : ℕ) (hn : n ≤ A.card) (d : Cell (scheme sem n hn)) :
    ¬ GradedLe (A, n + 1) ((scheme sem n hn).cell d) :=
  RecursiveSourceCarrier.separated D (Profile sem) hp n hn d

end
end VaughtConjecture.Knight.CanonicalRecursiveInventory

namespace VaughtConjecture.Knight.CanonicalRecursiveContract
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

abbrev carrierAt (sem : Semantics D) (m : ℕ) (hA : m + 2 ≤ A.card) :=
  CanonicalRecursiveInventory.scheme sem (m + 2) hA
abbrev boundaryAt (sem : Semantics D) (m : ℕ) (hA : m + 2 ≤ A.card) :=
  CanonicalRecursiveInventory.boundary sem (m + 2) hA

structure StateAt (sem : Semantics D) (m : ℕ) (hA : m + 2 ≤ A.card) where
  rows : Semantics (carrierAt sem m hA)
  consistent : sem.IsConsistent → rows.IsConsistent
  proper_lawful : ∀ {J : Finset ι × ℕ}, ¬ A ⊆ J.1 →
    ∀ {p : Cell D → ExtOrd}, RespectsSemanticsBelow sem J (fun d => p d.1) →
    ∀ {r : Cell (carrierAt sem m hA) → ExtOrd},
      (∀ d, r (boundaryAt sem m hA d) = p d) →
      RespectsSemanticsBelow rows J (fun d => r d.1)
  full_short : ∀ c : Cell (carrierAt sem m hA), (carrierAt sem m hA).scope c = A →
    ∀ d : (carrierAt sem m hA).below ((carrierAt sem m hA).cell c),
      Short ((carrierAt sem m hA).grade c) (rows.E c d)
  sectionOf : ∀ {K : ℕ}, m + 2 ≤ K → ∀ {p : Cell D → ExtOrd},
    RespectsSemanticsBelow sem (A, K) (fun d => p d.1) → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell (carrierAt sem m hA) → ExtOrd
  section_boundary : ∀ {K} (hK : m + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis (m + 2) z) → SelfVis (m + 2) C → ∀ d,
      sectionOf hK (p := p) hpr ht G C (boundaryAt sem m hA d) = p d
  section_lawful : ∀ {K} (hK : m + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis (m + 2) z) → SelfVis (m + 2) C →
      RespectsSemanticsBelow rows (A, K) (fun d => sectionOf hK (p := p) hpr ht G C d.1)
  section_bound : ∀ {K} (hK : m + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    SelfVis (m + 2) C → (∀ d, p d ≤ C) → ∀ d, sectionOf hK (p := p) hpr ht G C d ≤ C
  section_supported : ∀ {K} (hK : m + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd} {L : ℕ},
    m + 2 ≤ L → C ∈ G → ∀ d,
      OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (sectionOf hK (p := p) hpr ht G C d)
  section_agreement : ∀ {K} (hK : m + 2 ≤ K) {p q : Cell D → ExtOrd}
    (hpr) (htp) (hqr) (htq) {G : Finset ExtOrd} {C h : ExtOrd},
    (∀ z ∈ G, SelfVis (m + 2) z) → SelfVis (m + 2) C → h ∈ G → h ≤ C →
    Agree p q h → Agree (sectionOf hK (p := p) hpr htp G C)
      (sectionOf hK (p := q) hqr htq G C) h

abbrev carrier (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  carrierAt sem (n + 1) hA
abbrev boundary (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  boundaryAt sem (n + 1) hA
abbrev State (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  StateAt sem (n + 1) hA

def pairState (sem : Semantics D) (hA : 2 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A) :
    StateAt sem 0 hA where
  rows := CanonicalPairLocalSections.semantics sem hA hp
  consistent := CanonicalPairBoundary.consistent sem 1 2 (by decide)
    (CanonicalPairLocalSections.one_le hA) (by decide) hA hp (by decide)
  proper_lawful := CanonicalPairLocalSections.proper_lawful sem hA hp
  full_short := CanonicalPairLocalSections.full_short sem hA hp
  sectionOf := CanonicalPairLocalSections.sectionOf sem hA hp
  section_boundary := fun {_} hK {_} hpr ht {_ _} _ _ =>
    CanonicalPairLocalSections.section_old sem hA hp hK hpr ht
  section_lawful := fun {_} hK {_} hpr ht {_ _} =>
    CanonicalPairLocalSections.section_lawful sem hA hp hK hpr ht
  section_bound := fun {_} hK {_} hpr ht {_ _} =>
    CanonicalPairLocalSections.section_bound sem hA hp hK hpr ht
  section_supported := fun {_} hK {_} hpr ht {_ _ _} =>
    CanonicalPairLocalSections.section_supported sem hA hp hK hpr ht
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    CanonicalPairLocalSections.section_agreement sem hA hp hK hpr htp hqr htq

end
end VaughtConjecture.Knight.CanonicalRecursiveContract

namespace VaughtConjecture.Knight.CanonicalRecursiveSemantics
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open CanonicalRecursiveContract SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

section Step
variable (sem : Semantics D) (m : ℕ) (hA : m + 3 ≤ A.card)
variable (hp : ∀ d : Cell D, D.scope d ≠ A)
abbrev predecessor := carrierAt sem m (Nat.le_of_succ_le hA)
variable (P : StateAt sem m (Nat.le_of_succ_le hA))
abbrev Profile := CanonicalRecursiveInventory.Profile sem (m + 3)
abbrev stepCarrier := SourceLayerCarrier.scheme (predecessor sem m hA) (Profile sem m)
  (m + 3) (Nat.succ_pos (m + 2)) hA
abbrev old (d : Cell (predecessor sem m hA)) :=
  SourceLayerCarrier.toCell (predecessor sem m hA) (Profile sem m)
    (m + 3) (Nat.succ_pos (m + 2)) hA (.inl d)
abbrev controller := SourceLayerCarrier.controller (predecessor sem m hA) (Profile sem m)
  (m + 3) (Nat.succ_pos (m + 2)) hA
include hp in
theorem separation (d : Cell (predecessor sem m hA)) :
    ¬ GradedLe (A, m + 3) ((predecessor sem m hA).cell d) :=
  CanonicalRecursiveInventory.separated sem hp (m + 2) (Nat.le_of_succ_le hA) d
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor sem m hA)
  (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA (separation sem m hA hp)
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor sem m hA)
  (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA (separation sem m hA hp)
abbrev member := (controllerEquiv sem m hA hp).symm
theorem member_controller (q : Profile sem m) :
    member sem m hA hp (controller sem m hA q) = q :=
  (controllerEquiv sem m hA hp).symm_apply_apply q
abbrev grid := sourceGrid (m + 3) (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling (m + 3) (Cell D)

theorem profile_lawful (q : Profile sem m) :
    RespectsSemanticsBelow sem (A, m + 3) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff D (m + 3) sem (A, m + 3) le_rfl _).mp
    (q.property.1.toBelow (A, m + 3))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (m + 3) (A, m + 3) le_rfl).apply_symm_apply d))).symm

theorem profile_proper (q : Profile sem m) (d : Cell D) : q.val d ≠ ⊤ := q.property.2.2 d

abbrev selected (q : Profile sem m) := P.sectionOf (by omega : m + 2 ≤ m + 3)
  (profile_lawful sem m q) (profile_proper sem m q)
  (grid (D := D) m) (ceiling (D := D) m)

theorem selected_lawful (q : Profile sem m) :
    RespectsSemanticsBelow P.rows (A, m + 3)
      (fun d => selected sem m hA P q d.1) :=
  P.section_lawful (by omega) (profile_lawful sem m q) (profile_proper sem m q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : m + 2 ≤ m + 3))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : m + 2 ≤ m + 3))

theorem selected_bound (q : Profile sem m) (d : Cell (predecessor sem m hA)) :
    selected sem m hA P q d ≤ ceiling (D := D) m :=
  P.section_bound (by omega) (profile_lawful sem m q) (profile_proper sem m q)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : m + 2 ≤ m + 3))
    (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D (m + 3) sem) (m + 3)
      (Cell D) (GradeCutBoundary.toCell D (m + 3)) q) d

theorem selected_agreement (p q : Profile sem m) {h : ExtOrd}
    (hh : h ∈ grid (D := D) m) (hag : Agree p.val q.val h) :
    Agree (selected sem m hA P p) (selected sem m hA P q) h :=
  P.section_agreement (by omega) (profile_lawful sem m p) (profile_proper sem m p)
    (profile_lawful sem m q) (profile_proper sem m q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : m + 2 ≤ m + 3))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : m + 2 ≤ m + 3))
    hh (CanonicalFieldLayer.grid_bound (m + 3) (Cell D) hh) hag

theorem selected_supported (q : Profile sem m) (d : Cell (predecessor sem m hA)) :
    OrbitPrefixSupport.Supported (m + 3) (grid (D := D) m : Set ExtOrd) q.val
      (selected sem m hA P q d) :=
  P.section_supported (by omega) (profile_lawful sem m q) (profile_proper sem m q)
    (by omega) (sourceGrid_endpoint le_rfl) d

def lower (q : Profile sem m) (d : Cell (stepCarrier sem m hA)) : ExtOrd :=
  match SourceLayerCarrier.toOcc (predecessor sem m hA) (Profile sem m)
      (m + 3) (Nat.succ_pos (m + 2)) hA d with
  | .inl x => selected sem m hA P q x
  | .inr _ => ⊥

theorem lower_old (q : Profile sem m) (d : Cell (predecessor sem m hA)) :
    lower sem m hA P q (old sem m hA d) = selected sem m hA P q d := by
  change lower sem m hA P q
    (SourceLayerCarrier.toCell (predecessor sem m hA) (Profile sem m)
      (m + 3) (Nat.succ_pos (m + 2)) hA (.inl d)) = _
  simp only [lower, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data (stepCarrier sem m hA) (m + 3) (Cell D) where
  base := SeparatedSourceLayerCarrier.base (predecessor sem m hA) (Profile sem m) (m + 3)
    (Nat.succ_pos (m + 2)) hA (separation sem m hA hp) P.rows
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact separation sem m hA hp x
  grid := grid (D := D) m
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling (D := D) m
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound (m + 3) (Cell D) hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem m hA hp c).val
  lower c := lower sem m hA P (member sem m hA hp c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA d hd
    rw [lower_old]
    exact selected_bound sem m hA P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA (separation sem m hA hp) P.rows x _).mpr
    change RespectsSemanticsBelow P.rows _
      (fun d => lower sem m hA P _ (old sem m hA d.1))
    have hx : GradedLe ((predecessor sem m hA).cell x) (A, m + 3) :=
      ⟨(predecessor sem m hA).isPlan.subset_of_mem ((predecessor sem m hA).scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]
          using hg⟩
    simpa only [lower_old, CellScheme.below.mono] using
      (selected_lawful sem m hA P _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA d hd
    simpa only [lower_old] using selected_agreement sem m hA P _ _ hh hag x

abbrev stepRows := (data sem m hA hp P).rows
abbrev source (q : Profile sem m) := (data sem m hA hp P).profile (controller sem m hA q)
abbrev stepBoundary (d : Cell D) :=
  old sem m hA (boundaryAt sem m (Nat.le_of_succ_le hA) d)

theorem source_old (q : Profile sem m) (d : Cell (predecessor sem m hA)) :
    source sem m hA hp P q (old sem m hA d) = selected sem m hA P q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separation sem m hA hp) d)]
  change lower sem m hA P (member sem m hA hp (controller sem m hA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Profile sem m) (d : Cell D) :
    source sem m hA hp P q (stepBoundary sem m hA d) = q.val d := by
  rw [source_old]
  exact P.section_boundary (by omega) (profile_lawful sem m q) (profile_proper sem m q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : m + 2 ≤ m + 3))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl))
      (by omega : m + 2 ≤ m + 3)) d

theorem source_supported (q : Profile sem m) (d : Cell (stepCarrier sem m hA)) :
    OrbitPrefixSupport.Supported (m + 3) (grid (D := D) m : Set ExtOrd) q.val
      (source sem m hA hp P q d) := by
  by_cases hd : (stepCarrier sem m hA).cell d = (A, m + 3)
  · exact Or.inr (Or.inl (by
      change (data sem m hA hp P).profile _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (m + 3)).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA d hd
    rw [source_old]
    exact selected_supported sem m hA P q x

theorem source_short (q : Profile sem m) (d : Cell (stepCarrier sem m hA)) :
    Short (m + 3) (source sem m hA hp P q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short (m + 3) (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D (m + 3) sem) (m + 3)
      (Cell D) (GradeCutBoundary.toCell D (m + 3)) q) (source_supported sem m hA hp P q d)

theorem source_agreement_all (p q : Profile sem m) {h : ExtOrd}
    (hh : h ∈ grid (D := D) m) (hag : Agree p.val q.val h) :
    Agree (source sem m hA hp P p) (source sem m hA hp P q) h := by
  intro d
  by_cases hd : (stepCarrier sem m hA).cell d = (A, m + 3)
  · have hb : GradedLe ((stepCarrier sem m hA).cell d) (A, m + 3) := by
      rw [hd]; exact GradedLe.refl _
    exact (data sem m hA hp P).profile_prefix hh
      (by simpa only [data, member_controller] using hag) ⟨d, hb⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA d hd
    simpa only [source_old] using selected_agreement sem m hA P p q hh hag x

theorem inherited_row (c : Cell (predecessor sem m hA))
    (d : (predecessor sem m hA).below ((predecessor sem m hA).cell c)) :
    (stepRows sem m hA hp P).E (old sem m hA c) (ownerEquiv sem m hA hp c d) =
      P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (separation sem m hA hp) c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem step_consistent (hs : sem.IsConsistent) : (stepRows sem m hA hp P).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
    (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (predecessor sem m hA)
    (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA (separation sem m hA hp) P.rows x _).mpr
  have he : (data sem m hA hp P).base.E (old sem m hA x) ∘ ownerEquiv sem m hA hp x =
      P.rows.E x := funext (fun d => SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d)
  rw [he]
  exact P.consistent hs x

abbrev equiv (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, m + 3) J) :=
  HighLayerBountiful.equiv (predecessor sem m hA) (Profile sem m)
    (m + 3) (Nat.succ_pos (m + 2)) hA J hJ

theorem respects_iff (J : Finset ι × ℕ) (hJ : ¬ GradedLe (A, m + 3) J)
    (p : (predecessor sem m hA).below J → ExtOrd) :
    RespectsSemanticsBelow P.rows J p ↔
      RespectsSemanticsBelow (stepRows sem m hA hp P) J (p ∘ (equiv sem m hA J hJ).symm) := by
  apply respects_iff_of_equiv (equiv sem m hA J hJ)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell
      (predecessor sem m hA) (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA J hJ d)).symm)
    (fun d e => ?_) (fun b d _ => (inherited_row sem m hA hp P b.1 d).symm) p
  simp only [CellScheme.scope, equiv, HighLayerBountiful.equiv_cell]

theorem proper_lawful {J : Finset ι × ℕ} (hJ : ¬ A ⊆ J.1) {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem J (fun d => p d.1))
    {r : Cell (stepCarrier sem m hA) → ExtOrd}
    (hread : ∀ d, r (stepBoundary sem m hA d) = p d) :
    RespectsSemanticsBelow (stepRows sem m hA hp P) J (fun d => r d.1) := by
  have hl := P.proper_lawful hJ hpr (r := fun d => r (old sem m hA d)) hread
  let e := equiv sem m hA J (fun h => hJ h.1)
  have he : (fun d : (stepCarrier sem m hA).below J => r d.1) =
      (fun d : (predecessor sem m hA).below J => r (old sem m hA d.1)) ∘ e.symm := by
    funext d
    obtain ⟨a, rfl⟩ := e.surjective d
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rfl
  rw [he]
  exact (respects_iff sem m hA hp P J (fun h => hJ h.1) _).mp hl

theorem full_source_short (c : Cell (stepCarrier sem m hA))
    (hc : (stepCarrier sem m hA).scope c = A)
    (d : (stepCarrier sem m hA).below ((stepCarrier sem m hA).cell c)) :
    Short ((stepCarrier sem m hA).grade c) ((stepRows sem m hA hp P).E c d) := by
  by_cases he : (stepCarrier sem m hA).cell c = (A, m + 3)
  · obtain ⟨q, hq⟩ := (controllerEquiv sem m hA hp).surjective ⟨c, he⟩
    have hv : (controller sem m hA q).1 = c := congrArg Subtype.val hq
    have hr := (data sem m hA hp P).row_new (controller sem m hA q)
    subst c
    rw [hr, show (stepCarrier sem m hA).grade (controller sem m hA q).1 = m + 3 from
      congrArg Prod.snd (controller sem m hA q).2]
    exact source_short sem m hA hp P q d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence (predecessor sem m hA)
      (Profile sem m) (m + 3) (Nat.succ_pos (m + 2)) hA c he
    obtain ⟨e, rfl⟩ := (ownerEquiv sem m hA hp x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell (predecessor sem m hA) (Profile sem m)
      (m + 3) (Nat.succ_pos (m + 2)) hA (.inl x)
    change Short ((stepCarrier sem m hA).grade (old sem m hA x)) _
    rw [show (stepCarrier sem m hA).grade (old sem m hA x) = (predecessor sem m hA).grade x
      from congrArg Prod.snd hi]
    exact P.full_short x ((congrArg Prod.fst hi).symm.trans hc) e

variable {K : ℕ} (hK : m + 3 ≤ K) {p : Cell D → ExtOrd}
variable (hpr : RespectsSemanticsBelow sem (A, K) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)

abbrev normalized : Profile sem m := CanonicalRecursiveInventory.encode sem m
  (hpr.mono (show GradedLe (A, m + 3) (A, K) from ⟨Finset.Subset.refl _, hK⟩)) ht

def sectionOf (G : Finset ExtOrd) (C : ExtOrd) (d : Cell (stepCarrier sem m hA)) : ExtOrd :=
  PairedSlotDecoder.decode (m + 3) (values p) G C
    (source sem m hA hp P (normalized sem m hK hpr ht) d)

variable {G : Finset ExtOrd} {C : ExtOrd}

theorem section_boundary (hG : ∀ z ∈ G, SelfVis (m + 3) z) (hC : SelfVis (m + 3) C) (d : Cell D) :
    sectionOf sem m hA hp P hK hpr ht G C (stepBoundary sem m hA d) = p d := by
  rw [sectionOf, source_boundary]
  exact PairedSlotDecoder.decode_normalize hG hC ht d

theorem section_lawful (hG : ∀ z ∈ G, SelfVis (m + 3) z) (hC : SelfVis (m + 3) C) :
    RespectsSemanticsBelow (stepRows sem m hA hp P) (A, K)
      (fun d => sectionOf sem m hA hp P hK hpr ht G C d.1) := by
  have hproper (c : Cell (stepCarrier sem m hA)) (hc : (stepCarrier sem m hA).scope c ≠ A)
      (hg : (stepCarrier sem m hA).grade c ≤ K) :
      RespectsSemanticsBelow (stepRows sem m hA hp P) ((stepCarrier sem m hA).cell c)
        (fun d => sectionOf sem m hA hp P hK hpr ht G C d.1) :=
    proper_lawful sem m hA hp P
      (fun ha => hc (Finset.Subset.antisymm
        ((stepCarrier sem m hA).isPlan.subset_of_mem
          ((stepCarrier sem m hA).scope_mem_plan c)) ha))
      (hpr.mono ⟨(stepCarrier sem m hA).isPlan.subset_of_mem
        ((stepCarrier sem m hA).scope_mem_plan c), hg⟩)
      (section_boundary sem m hA hp P hK hpr ht hG hC)
  have hl : RespectsSemanticsBelow (stepRows sem m hA hp P) (A, m + 3)
      (fun d => sectionOf sem m hA hp P hK hpr ht G C d.1) := by
    apply (data sem m hA hp P).decoded_respects (controller sem m hA (normalized sem m hK hpr ht))
      le_rfl (PairedSlotDecoder.decode_witness hG hC) _
      (fun c hc => full_source_short sem m hA hp P c.1 hc)
    intro c hc
    have he : (stepCarrier sem m hA).cell c.1 ≠ (A, m + 3) := fun he => hc (congrArg Prod.fst he)
    have hr := ((data sem m hA hp P).old_respects_iff he).mp (hproper c.1 hc (c.2.2.trans hK))
    change RespectsSemanticsBelow (data sem m hA hp P).base _
      (fun d => PairedSlotDecoder.decode (m + 3) (values p) G C
        ((data sem m hA hp P).profile _ d.1)) at hr
    simpa only [ScopedSourcePrefixLayer.Data.profile_old _ _
      ((data sem m hA hp P).below_old he _)] using hr
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro c
  by_cases hc : (stepCarrier sem m hA).scope c.1 = A
  · have hg := RecursiveSourceCarrier.full_grade D (CanonicalRecursiveInventory.Profile sem)
      hp (m + 3) hA c.1 hc
    exact hl.mono ⟨(stepCarrier sem m hA).isPlan.subset_of_mem
      ((stepCarrier sem m hA).scope_mem_plan c.1), hg⟩
  · exact hproper c.1 hc c.2.2

theorem section_bound (hC : SelfVis (m + 3) C) (hb : ∀ d, p d ≤ C)
    (d : Cell (stepCarrier sem m hA)) : sectionOf sem m hA hp P hK hpr ht G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨d, hd⟩ := mem_values.mp ha
  simpa only [hd] using hb d

theorem section_supported {L : ℕ} (hL : m + 3 ≤ L) (hCG : C ∈ G)
    (d : Cell (stepCarrier sem m hA)) :
    OrbitPrefixSupport.Supported L (G : Set ExtOrd) p
      (sectionOf sem m hA hp P hK hpr ht G C d) := PairedSlotDecoder.decode_supported hL hCG _

theorem section_agreement {q : Cell D → ExtOrd}
    (hqr : RespectsSemanticsBelow sem (A, K) (fun d => q d.1)) (htq : ∀ d, q d ≠ ⊤)
    {h : ExtOrd} (hG : ∀ z ∈ G, SelfVis (m + 3) z) (hC : SelfVis (m + 3) C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf sem m hA hp P hK hpr ht G C) (sectionOf sem m hA hp P hK hqr htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_agreement_all sem m hA hp P
    (normalized sem m hK hpr ht) (normalized sem m hK hqr htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun d _ => hcompare _)

def successor : StateAt sem (m + 1) hA where
  rows := stepRows sem m hA hp P
  consistent := step_consistent sem m hA hp P
  proper_lawful := proper_lawful sem m hA hp P
  full_short := full_source_short sem m hA hp P
  sectionOf := sectionOf sem m hA hp P
  section_boundary := section_boundary sem m hA hp P
  section_lawful := section_lawful sem m hA hp P
  section_bound := section_bound sem m hA hp P
  section_supported := section_supported sem m hA hp P
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    section_agreement sem m hA hp P hK hpr htp hqr htq

end Step

variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

def stateAt : (m : ℕ) → (hA : m + 2 ≤ A.card) → StateAt sem m hA
  | 0, hA => pairState sem hA hp
  | m + 1, hA => successor sem m hA hp (stateAt m (Nat.le_of_succ_le hA))

abbrev rowsAt (m : ℕ) (hA : m + 2 ≤ A.card) := (stateAt sem hp m hA).rows

theorem consistentAt (hs : sem.IsConsistent) (m : ℕ) (hA : m + 2 ≤ A.card) :
    (rowsAt sem hp m hA).IsConsistent := (stateAt sem hp m hA).consistent hs

abbrev state (n : ℕ) (hA : n + 3 ≤ A.card) : State sem n hA := stateAt sem hp (n + 1) hA
abbrev rows (n : ℕ) (hA : n + 3 ≤ A.card) := rowsAt sem hp (n + 1) hA

theorem consistent (hs : sem.IsConsistent) (n : ℕ) (hA : n + 3 ≤ A.card) :
    (rows sem hp n hA).IsConsistent := consistentAt sem hp hs (n + 1) hA

end
end VaughtConjecture.Knight.CanonicalRecursiveSemantics
