/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Logic
public import ThreeSumApsp.Lang.Regions
public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Util.List
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Tactic.Positivity

/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light



/-- The cells a, a + 1, … of the memory μ hold the list l. -/
def Seg (μ : Light.Memory) a (l : List ℤ) := ∀ i (h : i < l.length), μ (a + i) = l[i]

variable {μ μ' μ'' : Light.Memory} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}

@[simp] theorem Seg.nil : Seg μ a [] := fun i h => absurd h (by simp)

/-- Reading a cell of a segment. -/
def Seg.get (h : Seg μ a l) {i} hi := h i hi

variable (h : Seg μ a l)

include h in
/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD {i} (hi : i < l.length) d : μ (a + i) = l.getD i d := by
  aesop

theorem seg_cons : Seg μ a (x :: l) ↔ μ a = x ∧ Seg μ (a + 1) l := by
  constructor
  · intro h
    refine ⟨by have h0 := h 0 (by simp); rwa [Nat.add_zero, List.getElem_cons_zero] at h0,
      fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
  · grind [Light.Seg]

theorem seg_append : Seg μ a (l₁ ++ l₂) ↔ Seg μ a l₁ ∧ Seg μ (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp; omega), List.getElem_append_left hi]
    · simp_all [Light.Seg, Nat.add_assoc]
  · grind [Light.Seg]

include h in
theorem Seg.take k : Seg μ a (l.take k) := fun i hi => by
  aesop

include h in
theorem Seg.drop k : Seg μ (a + k) (l.drop k) := fun i hi => by
  ram_safe [Light.Seg]

include h in
/-- A segment only depends on its own cells. -/
theorem Seg.congr (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

/-- A segment stays where it is if its cells do not change.  By the default proof of `hs`, the term
`h.keep` carries `h` to a later memory across the steps whose promises are in the context. -/
def Seg.keep (h : Seg μ a l) (hs : SameOn (Inside a l.length) μ μ' := by light_keep) :=
  h.congr fun i hi => hs _ ⟨by omega, by omega⟩

include h in
/-- Writing into a segment. -/
theorem Seg.update_in {i} (hi : i < l.length) x :
    Seg (Function.update μ (a + i) x) a (l.set i x) := by
  ram_safe [Light.Seg]

include h in
/-- Writing outside a segment. -/
theorem Seg.update_out (hb : b < a ∨ a + l.length ≤ b) x :
    Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

include h in
/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc x : Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  seg_append.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [seg_cons]⟩

/-- A segment all of whose cells are kept. -/
def Seg.of_sameOn {K} (h : Seg μ b l) (hs : SameOn K μ μ')
    (hK : ∀ i < l.length, K (b + i)) := h.congr fun i hi => hs _ (hK i hi)

theorem SameOutside.refl : SameOutside μ μ a n := SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n'} (h : SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) x :
    SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc

theorem SameOutside2.refl {m} : SameOutside2 μ μ a n b m := SameOn.refl

/-- A segment that does not meet the region is kept. -/
def Seg.of_sameOutside (h : Seg μ b l) (hs : SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) :=
  h.congr fun i hi => hs _ (by omega)

/-- The cells a, a + 1, … hold a list of natural numbers. -/
abbrev SegN (μ : Light.Memory) (a : ℕ) (l : List ℕ) : Prop := Seg μ a (l.map fun x : ℕ => x)

/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l} (h : SegN μ a l) {i} (hi : i < l.length) :
    μ (a + i) = (l.getD i 0 : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l} (h : SegN μ a l) {i} hi :
    μ (a + i) = l[i] := by
  rw [h i (by simpa using hi), List.getElem_map]

/-- Writing just after a segment of natural numbers makes it longer. -/
theorem SegN.snoc {l} (h : SegN μ a l) (x : ℕ) :
    SegN (Function.update μ (a + l.length) x) a (l ++ [x]) := by
  simpa [SegN] using Seg.snoc h x

/-- One more entry of a list of natural numbers is written behind its first k entries. -/
theorem SegN.take_succ {l : List ℕ} {k} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) (l.getD k 0 : ℕ)) a (l.take (k + 1)) := by
  have hsnoc := h.snoc (l.getD k 0)
  rwa [List.length_take, Nat.min_eq_left hk.le, ← List.take_succ_getD l hk 0] at hsnoc

/-- A piece of a segment of natural numbers: w cells from the place lo on. -/
theorem SegN.drop_take {l} (h : SegN μ a l) lo w :
    SegN μ (a + lo) ((l.drop lo).take w) := by
  simpa only [SegN, List.map_take, List.map_drop] using (Seg.drop h lo).take w

/-- A segment of natural numbers stays where it is if its cells do not change. -/
theorem SegN.keep {l} (h : SegN μ a l)
    (hs : SameOn (Inside a l.length) μ μ' := by light_keep) : SegN μ' a l :=
  Seg.keep h (by simpa using hs)

/-- A segment of natural numbers that does not meet the region is kept. -/
def SegN.of_sameOutside {l} (h : SegN μ b l) (hs : SameOutside μ μ' a n)
     hd :=
  Seg.of_sameOutside h hs (by simpa using hd)

/-- The cells from a on hold the matrix A, row by row. -/
def MatAt {n k} (μ : Light.Memory) (a : ℕ) (A : ThreeSumApsp.IntMatrix n k) : Prop :=
  ∀ (i : Fin n) (j : Fin k), μ (a + i * k + j) = A i j

/-- A matrix stays where it is if its cells do not change. -/
theorem MatAt.congr {n k} {A : ThreeSumApsp.IntMatrix n k} (h : MatAt μ a A)
    (he : ∀ b, a ≤ b → b < a + n * k → μ' b = μ b) : MatAt μ' a A := fun i j => by
  have := Nat.mul_add_lt_mul i.isLt j.isLt
  rw [he _ (by omega) (by omega)]
  exact h i j

/-- A matrix that lies below e is still there in a memory that agrees below e. -/
def MatAt.congr_below {n k e} {A : ThreeSumApsp.IntMatrix n k} (h : MatAt μ a A)
    (hlow : ∀ x < e, μ' x = μ x) (hle : a + n * k ≤ e) :=
  h.congr fun b _ hb => hlow b (by omega)

end Light
