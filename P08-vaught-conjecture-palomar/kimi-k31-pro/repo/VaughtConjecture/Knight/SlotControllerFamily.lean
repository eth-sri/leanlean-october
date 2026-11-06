/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreshSourceSlots

/-! # Joint rows for an arbitrary finite family of insertion slots

Old levels occupy even blocks and one independent fresh reading occupies an
odd block. Controllers read each other at their first order disagreement.
The two directed cross-readings need not coincide. All incoming row-family
localities follow from a natural-number source-order identity and explicit
faithful interpolation. No transformation is composed.

This is a grade-one row layer, not a support plan or a bountiful domain.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SlotControllerFamily

open Transform Value ExtOrd FreshSourceSlots

/-- Bottom occurrence, fresh occurrence, old levels, and the slot controllers. -/
abbrev Point (n : ℕ) := Option (Option (Fin n)) ⊕ Fin (n + 1)

def bottomPoint {n : ℕ} : Point n := .inl none
def fresh {n : ℕ} : Point n := .inl (some none)
def old {n : ℕ} (i : Fin n) : Point n := .inl (some (some i))
def controller {n : ℕ} (j : Fin (n + 1)) : Point n := .inr j

def height (n : ℕ) : ℕ := 2 * n + 4

/-- The first divergence is read in the owner's source order, not symmetrically. -/
def cross {n : ℕ} (q p : Fin (n + 1)) : ℕ :=
  if q = p then height n else if p < q then 2 * p.val + 2 else 2 * q.val + 1

def index {n : ℕ} (q : Fin (n + 1)) : Point n → ℕ
  | .inl none => 0
  | .inl (some none) => 2 * q.val + 1
  | .inl (some (some i)) => 2 * i.val + 2
  | .inr p => cross q p

theorem cross_pos {n : ℕ} (q p : Fin (n + 1)) : 0 < cross q p := by
  unfold cross height
  split_ifs <;> omega

theorem index_zero_iff {n : ℕ} (q : Fin (n + 1)) (d : Point n) :
    index q d = 0 ↔ d = bottomPoint := by
  rcases d with (_ | (_ | d)) | d
  · simp [index, bottomPoint]
  · simp [index, bottomPoint]
  · simp [index, bottomPoint]
  · simp only [index, bottomPoint, Sum.inr_ne_inl, iff_false]
    exact Nat.ne_of_gt (cross_pos q d)

theorem index_le_height {n : ℕ} (q : Fin (n + 1)) (d : Point n) :
    index q d ≤ height n := by
  rcases d with (_ | (_ | d)) | d
  · exact Nat.zero_le _
  · have hq := q.isLt
    simp only [index, height]
    omega
  · have hd := d.isLt
    simp only [index, height]
    omega
  · have hq := q.isLt
    have hd := d.isLt
    simp only [index, cross, height]
    split_ifs <;> omega

@[simp] theorem index_diagonal {n : ℕ} (q : Fin (n + 1)) :
    index q (controller q) = height n := by simp [index, controller, cross]

set_option maxHeartbeats 1200000 in
-- The finite point-class and directed-cross cases require many Presburger branches.
/-- Every upper row, capped at its actual reading of a lower controller,
is ordered by that controller's source table, on every occurrence. -/
theorem capped_order {n : ℕ} (p q : Fin (n + 1)) (d e : Point n)
    (h : index p d ≤ index p e) :
    min (index q d) (cross q p) ≤ min (index q e) (cross q p) := by
  have hp := p.isLt
  have hq := q.isLt
  rcases d with (_ | (_ | d)) | d <;>
    rcases e with (_ | (_ | e)) | e <;>
    simp only [index, cross, height] at h ⊢ <;>
    split_ifs at * <;> omega

noncomputable def value (i : ℕ) : ExtOrd :=
  if i = 0 then ⊥ else SeparatedGradeOne.band i

theorem value_visible (i : ℕ) : SelfVis 1 (value i) := by
  unfold value
  split_ifs
  · exact selfVis_bot 1
  · exact SeparatedGradeOne.band_visible i

theorem value_coded (i : ℕ) : IsCodedLabel 1 (value i) := by
  unfold value
  split_ifs
  · exact Or.inl rfl
  · exact SeparatedGradeOne.band_coded i 1

theorem value_le_iff (i j : ℕ) : value i ≤ value j ↔ i ≤ j := by
  by_cases hi : i = 0
  · simp [value, hi]
  by_cases hj : j = 0
  · simp [value, hi, hj, SeparatedGradeOne.band]
  simp only [value, ite_eq_right hi, ite_eq_right hj, band_le_iff]

theorem value_mono : Monotone value := fun i j h => (value_le_iff i j).mpr h

noncomputable def row {n : ℕ} (q : Fin (n + 1)) (d : Point n) : ExtOrd := value (index q d)

noncomputable def label {n : ℕ} (q : Fin (n + 1)) (f : ℕ → ExtOrd)
    (d : Point n) : ExtOrd := f (index q d)

/-- Any ordered, visible table with bottom at index zero is a faithful target
of the corresponding row. The witness is constructed directly. -/
theorem transforms_of_order {n : ℕ} (p : Fin (n + 1)) (t : Point n → ExtOrd)
    (hv : ∀ d, SelfVis 1 (t d)) (hb : t bottomPoint = ⊥)
    (hm : ∀ d e, index p d ≤ index p e → t d ≤ t e) :
    TransformsTo (fun _ : Point n => 1) (row p) t := by
  classical
  let r : Point n → Option ℕ := fun d => if index p d = 0 then none else some (index p d)
  have hr : ∀ d, source (r d) = row p d := by
    intro d
    dsimp only [r, row, value]
    split_ifs <;> rfl
  have hbot : ∀ d, r d = none → t d = ⊥ := by
    intro d hd
    by_cases hz : index p d = 0
    · exact (index_zero_iff p d).mp hz ▸ hb
    · simp only [r, ite_eq_right hz, Option.some_ne_none] at hd
  apply (decoder_witness r t hv).transformsTo
  intro d
  rw [gTop_of_le le_rfl, min_top_right, ← hr d]
  apply (decoder_read r t ?_ hbot d).symm
  intro a b hab
  rw [hr a, hr b] at hab
  exact hm a b ((value_le_iff _ _).mp hab)

/-- All sibling localities hold for a single ordered branch. These are the
actual controller caps of this labelling, not freely chosen overlap caps. -/
theorem label_locality {n : ℕ} (p q : Fin (n + 1)) (f : ℕ → ExtOrd)
    (hm : Monotone f) (hb : f 0 = ⊥) (hv : ∀ d : Point n, SelfVis 1 (label q f d)) :
    TransformsTo (fun _ : Point n => 1) (row p)
      (fun d => min (label q f d) (label q f (controller p))) := by
  apply transforms_of_order
  · intro d
    exact selfVis_min (hv d) (hv (controller p))
  · simp only [label, bottomPoint, index, hb, min_bot_left]
  · intro d e h
    change min (f (index q d)) (f (cross q p)) ≤ min (f (index q e)) (f (cross q p))
    rw [← hm.map_min, ← hm.map_min]
    exact hm (capped_order p q d e h)

/-- All controller localities and full-index availability, with distinct
occurrences retained. Proper-index availability is not part of this predicate. -/
def Joint {n : ℕ} (p : Point n → ExtOrd) : Prop :=
  (∀ d, SelfVis 1 (p d)) ∧ p bottomPoint = ⊥ ∧
  (∀ c, TransformsTo (fun _ : Point n => 1) (row c)
    (fun d => min (p d) (p (controller c)))) ∧
  ∀ d, ∃ c, p d ≤ p (controller c)

theorem label_joint {n : ℕ} (q : Fin (n + 1)) (f : ℕ → ExtOrd)
    (hm : Monotone f) (hb : f 0 = ⊥) (hv : ∀ d : Point n, SelfVis 1 (label q f d)) :
    Joint (label q f) := by
  refine ⟨hv, hb, fun c => label_locality c q f hm hb hv, ?_⟩
  intro d
  refine ⟨q, ?_⟩
  change f (index q d) ≤ f (index q (controller q))
  rw [index_diagonal]
  exact hm (index_le_height q d)

/-- Every row is jointly consistent with every controller and supplies
availability at the common full index, for arbitrary family size. -/
theorem rows_joint {n : ℕ} (q : Fin (n + 1)) : Joint (row q) :=
  label_joint q value value_mono rfl (fun _ => value_visible _)

end VaughtConjecture.Knight.SlotControllerFamily
