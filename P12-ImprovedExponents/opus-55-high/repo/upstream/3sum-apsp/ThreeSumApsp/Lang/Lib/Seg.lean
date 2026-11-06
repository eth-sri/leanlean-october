/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Lang.Logic
import ThreeSumApsp.Lang.Regions
import ThreeSumApsp.Util.Index
import ThreeSumApsp.Util.List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Positivity

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/


namespace Light


/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]

/-- The list held by the n cells from address a. -/
def readSeg (μ : ℕ → ℤ) (a n : ℕ) : List ℤ := (List.range n).map fun i => μ (a + i)

variable {μ μ' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

variable {i : ℕ}

@[simp] theorem length_readSeg : (readSeg μ a n).length = n := by simp [readSeg]

@[simp] theorem getElem_readSeg (h : i < (readSeg μ a n).length) :
    (readSeg μ a n)[i] = μ (a + i) := by
  simp [readSeg]

@[simp] theorem Seg.nil : Seg μ a [] := by tauto

/-- Reading a cell of a segment. -/
theorem Seg.get (h : Seg μ a l) (hi : i < l.length) : μ (a + i) = l[i] := by aesop

/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : Seg μ a l) (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  aesop

/-- A segment determines its list. -/
theorem Seg.eq_readSeg (h : Seg μ a l) : l = readSeg μ a l.length :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by rw [getElem_readSeg, h]

theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); assumption,
      fun i hi => ?_⟩
    have := h (i + 1) (by simp_all)
    grind
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => assumption
    | succ i =>
      have := h i (by simp_all)
      grind

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by grind), List.getElem_append_left]
    · have := h (l₁.length + i) (by simp_all)
      grind
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < l₁.length
    · aesop
    · rw [List.getElem_append_right (by omega), ← h₂]
      simp_all

theorem Seg.take (h : Seg μ a l) (k : ℕ) : Seg μ a (l.take k) := fun i hi => by
  aesop

theorem Seg.drop (h : Seg μ a l) (k : ℕ) : Seg μ (a + k) (l.drop k) := fun i hi => by
  rw [List.getElem_drop, ← h, Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by aesop

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
theorem Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by light_keep) :
    Seg μ' a l :=
  h.congr fun i hi => by aesop

/-- Writing into a segment. -/
theorem Seg.update_in (h : Seg μ a l) (x : ℤ) :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  intro j hj
  by_cases hji : j = i
  · simp_all
  · rw [Function.update_of_ne (by omega), List.getElem_set_of_ne (by omega), h]

/-- Writing outside a segment. -/
theorem Seg.update_out (h : Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => by grind

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : Seg μ a l) (x : ℤ) : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
theorem Seg.of_sameOn {K : ℕ → Prop} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) : Seg μ' b l := h.congr fun i hi => by aesop

theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; aesop

theorem SameOutside2.refl {m : ℕ} : SameOutside2 μ μ a n b m := SameOn.refl

/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : ℕ → ℤ) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => (x : ℤ))

/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : SegN μ a l) (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simp_all), List.getElem_map, List.getD_eq_getElem _]

/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : SegN μ a l) (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simp_all), List.getElem_map]

/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l : List ℕ} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) (x : ℤ)) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h x

variable {k : ℕ}

/-- One more entry of a list of natural numbers is written behind its first k entries. -/
theorem SegN.take_succ {l : List ℕ} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) ((l.getD k 0 : ℕ) : ℤ)) a (l.take (k + 1)) := by
  have hsnoc := h.snoc (l.getD k 0)
  grind [List.length_take, Nat.min_eq_left, List.take_succ_getD]

/-- A piece of a segment of natural numbers: w cells from the place lo on. -/
theorem SegN.drop_take {l : List ℕ} (h : SegN μ a l) (lo w : ℕ) :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w

/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l : List ℕ} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by light_keep) : SegN μ' a l :=
  by grind [Seg.keep]

/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : SegN μ' b l :=
  Seg.of_sameOutside h hs (by simp_all)

/-- The cells from a on hold the matrix A, row by row. -/
def MatAt {n k : ℕ} (μ : ℕ → ℤ) (a : ℕ) (A : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  ∀ (i : Fin n) (j : Fin k), μ (a + i * k + j) = A i j

/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  aesop

/-- A matrix that lies below e is still there in a memory that agrees below e. -/
theorem MatAt.congr_below {n e : ℕ} {A : Matrix (Fin n) (Fin k) ℤ} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) : MatAt μ' a A :=
  h.congr fun b _ hb => by grind
