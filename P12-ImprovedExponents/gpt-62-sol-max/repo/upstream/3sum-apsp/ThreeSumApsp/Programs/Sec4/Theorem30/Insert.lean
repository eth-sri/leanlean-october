/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Inserting a string into a trie (Lemma 29)

"inserting them into the trie also takes O(L) operations per box, and adds at most L vertices per
box."  New vertices are taken from the end of the part of the trie area that is in use, whose length
is kept in the cell fp.  No routine relies on what the free part of the area holds: the eleven cells
of a new vertex are cleared.  Addresses are relative to the base of the area, so the models are
`Spec.trieNew` and `Spec.trieInsert`.

1. `Ends.clearLoop` is the rule for the loop that clears cells.  `TrieMem.new` and `TrieMem.set`
   say what the trie area holds after a new vertex has been cleared and after a cell has been
   written.
2. `newRoot_spec`: a new vertex as a root.
3. `alloc_spec`: a new vertex as a child.  `Insertion.child` is the array after the test for the
   child, and `Insertion.Progress.step` says that the insertion goes on from the child in that
   array.
4. `insert_spec`: the loop goes down one level in each round (`Insertion.Inv`,
   `Insertion.round_spec`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Clearing cells -/

/-- Writes 0 into the cells from the address in local x up to, and not including, the address in
local y. -/
def clearLoop (x y : ℕ) : Stmt :=
  .while (v x <' v y) (
    .store (v x) (k 0) ;;
    .set x (v x +' k 1))

/-- **The rule for clearLoop.**  The loop clears the n cells from a and changes no local but x. -/
theorem Ends.clearLoop (hs : Std lim) {x y a n T : ℕ} {loc μ : ℕ → ℤ} {Q : State → Prop}
    (hxy : y ≠ x) (hx : loc x = a) (hy : loc y = (a + n : ℕ)) (ha : a + n < lim.space)
    (done : Q ⟨Function.update loc x ((a + n : ℕ) : ℤ), wrote μ a (fun _ => 0) n⟩)
    (hT : n * 11 + 4 ≤ T := by light_time) : Ends lim P d (clearLoop x y) ⟨loc, μ⟩ T Q := by
  light_facts hs
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc x ((a + j : ℕ) : ℤ),
    wrote μ a (fun _ => 0) j⟩) n ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hx, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + j).toNat = a + j := by omega
    refine ⟨by simp, by simp_all, by light_side, ?_⟩
    rw [← wrote_succ]
    aesop
  simp_all

/-- The cells that have been cleared. -/
private theorem seg_wrote_zero (μ : ℕ → ℤ) (a n : ℕ) :
    Seg (wrote μ a (fun _ => 0) n) a (List.replicate n 0) := fun i hi => by
  rw [wrote_done (by simp_all), List.getElem_replicate]

/-! ## The trie area -/

section

variable {μ : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ}

/-- The trie area after a new vertex has been cleared behind the part in use and the free pointer
has been moved. -/
theorem TrieMem.new (h : TrieMem μ tr cap fp T) (hcap : T.length + 11 ≤ cap) :
    TrieMem (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp (trieNew T) ∧
      SameOutsideTrie μ
        (Function.update (wrote μ (tr + T.length) (fun _ => 0) 11) fp ((T.length + 11 : ℕ) : ℤ))
        tr cap fp := by
  have hfp := h.fp_out
  have hsame : SameOutside μ (wrote μ (tr + T.length) (fun _ => 0) 11) (tr + T.length) 11 :=
    sameOutside_wrote le_rfl
  refine ⟨⟨?_, ?_, ?_, hfp⟩, fun b ⟨hb, hbfp⟩ => ?_⟩
  · refine Seg.update_out (seg_append.2
      ⟨h.seg.keep, seg_wrote_zero _ _ _⟩) ?_ _
    grind
  · rw [Function.update_self, length_trieNew]
  · rw [length_trieNew]
    exact hcap
  · rw [Function.update_of_ne hbfp]
    exact hsame b (by omega)

/-- Writing into a cell of the part of the trie area that is in use. -/
theorem TrieMem.set (h : TrieMem μ tr cap fp T) {q : ℕ} (hq : q < T.length) (x : ℤ) :
    TrieMem (Function.update μ (tr + q) x) tr cap fp (T.set q x) ∧
      SameOutsideTrie μ (Function.update μ (tr + q) x) tr cap fp := by
  have hfp := h.fp_out
  have hcap := h.le_cap
  refine ⟨⟨h.seg.update_in hq x, ?_, by simp_all, hfp⟩,
    fun b hb => Function.update_of_ne (by omega) _ _⟩
  rw [Function.update_of_ne (by omega), h.free, List.length_set]

end

/-! ## A new root -/

namespace NewRoot

/-- The local variables of newRoot: the arguments (the base of the trie area and the address of the
free pointer), the address of the new vertex, and the two ends of its cells in the memory.  Local 0
also takes the result. -/
registers [Area / Result, Free, New, From, Upto]

end NewRoot

open NewRoot in
/-- newRoot(area, free): take a new vertex from the end of the part in use, clear its cells, move
the free pointer, and return the address of the vertex. -/
def newRootBody : Stmt :=
  .set New (M (v Free)) ;;
  .set From (v Area +' v New) ;;
  .set Upto (v From +' k 11) ;;
  clearLoop From Upto ;;
  .store (v Free) (v New +' k 11) ;;
  .set Result (v New)

/-- **newRoot** appends a new vertex to the array, and returns its address. -/
theorem newRoot_spec (hP : P[Proc.newRoot]? = some newRootBody) (hs : Std lim) :
    NewRootSpec lim P := by
  intro tr cap fp T μ hT hcap htr hfp
  refine fun d _ => ⟨newRootBody, hP, ?_⟩
  have hfree := hT.free
  light_facts hs
  unfold tNewRoot
  -- new := mem[free]; from := area + new; upto := from + 11
  light_steps using hfree
  -- clear the cells of the new vertex
  refine Ends.next _ (Ends.clearLoop hs (a := tr + T.length) (n := 11) (by decide) rfl rfl
    (by omega) ?_ (hT := le_rfl))
  rw [update_frame_setLocal]
  -- mem[free] := new + 11
  light_steps
  exact ⟨rfl, hT.new hcap⟩

/-! ## A new child -/

namespace Insertion

/-- The local variables of insert: the arguments (the base of the trie area, the root, which becomes
the current vertex, the address of the string, its length, the value, the address of the free
pointer), the level, the address of the cell with the pointer to the child, and, for a new vertex,
its address and the two ends of its cells in the memory. -/
registers [Area, Vertex, Key, Len, Value, Free, Level, Cell, New, From, Upto]

end Insertion

open Insertion

/-- A new vertex as the child in the current cell. -/
def allocStmt : Stmt :=
  .set New (M (v Free)) ;;
  .store (v Cell) (v New) ;;
  .set From (v Area +' v New) ;;
  .set Upto (v From +' k 11) ;;
  clearLoop From Upto ;;
  .store (v Free) (v New +' k 11)

/-! ## Insertion -/

/-- One round: find the cell with the pointer to the child, make a new child if there is none, and
go down to the child. -/
def insertRound : Stmt :=
  .set Cell (v Area +' v Vertex +' M (v Key +' v Level)) ;;
  .ite (M (v Cell) =' k 0) allocStmt .skip ;;
  .set Vertex (M (v Cell))

/-- insert(area, root, key, len, value, free): go down the string, making new children where there
are none, and write the value into the vertex that is reached. -/
def insertBody : Stmt :=
  Stmt.for Level (v Len) insertRound ;;
  .store (v Area +' v Vertex) (v Value)

namespace Insertion

/-- The pointer to a new child, read back from the array. -/
private theorem getD_trieNew_set {T : List ℤ} {q : ℕ} (hq : q < T.length) (x : ℤ) :
    (trieNew (T.set q x)).getD q 0 = x := by
  grind [trieNew]

/-- The array after the test for the child in the cell q: a new vertex has been appended if there
was no child. -/
def child (T : List ℤ) (q : ℕ) : List ℤ :=
  if T.getD q 0 = 0 then trieNew (T.set q T.length) else T

/-- After i levels the array is Ti and the current vertex p: what is left is the insertion of the
rest of the string from p. -/
structure Progress (T : List ℤ) (root : ℕ) (kl : List ℕ) (val : ℤ) (i : ℕ) (Ti : List ℤ) (p : ℕ) :
    Prop where
  ok : InsertOK Ti p (kl.drop i)
  eq : trieInsert T root kl val = trieInsert Ti p (kl.drop i) val
  /-- Each level has added at most one vertex. -/
  len : Ti.length ≤ T.length + 11 * i

section

variable {T Ti : List ℤ} {root i p : ℕ} {kl : List ℕ} {val : ℤ}

/-- The current vertex lies inside the array. -/
theorem Progress.inside (h : Progress T root kl val i Ti p) : p + 11 ≤ Ti.length := by
  have hok := h.ok
  generalize kl.drop i = rest at hok
  cases rest with
  | nil => exact hok.2
  | cons x rest => exact hok.2.1

/-- One level down: in the array with the child, the pointer to the child is positive, and the
insertion goes on from the child. -/
theorem Progress.step (h : Progress T root kl val i Ti p) (hi : i < kl.length)
    (hsym : kl[i] < 11) :
    0 < (child Ti (p + kl[i])).getD (p + kl[i]) 0 ∧
      Progress T root kl val (i + 1) (child Ti (p + kl[i]))
        ((child Ti (p + kl[i])).getD (p + kl[i]) 0).toNat := by
  have hin := h.inside
  have hlen := h.len
  have hok := h.ok
  have heq := h.eq
  rw [List.drop_eq_getElem_cons hi] at hok heq
  rw [trieInsert] at heq
  obtain ⟨hpos, -, hbranch⟩ := hok
  unfold child
  by_cases hz : Ti.getD (p + kl[i]) 0 = 0
  · -- there is no child: a new vertex at the end of the array
    rw [if_pos hz] at hbranch heq ⊢
    rw [getD_trieNew_set (by omega), Int.toNat_natCast]
    exact ⟨by omega, hbranch, heq, by rw [length_trieNew, List.length_set]; omega⟩
  · -- the child exists
    rw [if_neg hz] at hbranch heq ⊢
    exact ⟨hbranch.1, hbranch.2, heq, by omega⟩

end

end Insertion

/-- **insert** stores the value for the string: the area then holds `Spec.trieInsert`. -/
theorem insert_spec (hP : P[Proc.insert]? = some insertBody) (hs : Std lim) :
    InsertSpec lim P := by
  intro x μ pre d _
  refine .of_body hP ?_
  rw [InsertArgs.vals, ← pre.len]
  light_facts hs pre
  unfold tInsert
  let S (j : ℕ) (z : List ℤ × ℕ × ℤ × ℤ × ℤ × ℤ) ν : State :=
    ⟨frame [x.tr, z.2.1, x.key, x.kl.length, x.val, x.fp, j,
      z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, z.2.2.2.2.2], ν⟩
  let I j (z : List ℤ × ℕ × ℤ × ℤ × ℤ × ℤ) ν :=
    Progress x.T x.root x.kl x.val j z.1 z.2.1 ∧ TrieMem ν x.tr x.cap x.fp z.1 ∧
      SameOutsideTrie μ ν x.tr x.cap x.fp
  refine Ends.next _ (Ends.forShape S I x.kl.length 161 (x.T, x.root, 0, 0, 0, 0)
    ⟨⟨pre.walk, rfl, by simp⟩, pre.trie, .refl⟩ ?_ ?_ (first := ?_)
    (bound := by intros; simp [S]) (counter := by intros; rfl)
    (next := by intros; rw [update_frame_setLocal]; rfl) (hT := le_rfl)) (by light_time)
  · dsimp only [I]
    rintro i ⟨Ti, p, c, new, lo, hi⟩ ν hj ⟨hprog, hmem, hsame⟩
    dsimp at hprog hmem
    have hin := hprog.inside
    light_facts hmem hprog
    have hsym := pre.digits _ (List.getElem_mem hj)
    obtain ⟨hchild, hnext⟩ := hprog.step hj hsym
    have hcell := (hsame (x.key + i) ⟨by omega, by omega⟩).trans (pre.seg.getElem hj)
    have hq : p + x.kl[i] < Ti.length := by omega
    light_set (x.tr + (p + x.kl[i]) : ℕ) using hcell, S
    generalize p + x.kl[i] = q at hchild hnext hq ⊢
    have hptr := hmem.seg.getD hq 0
    refine Ends.pieceThen (T₁ := 149) (R := fun σ => ∃ (a b c : ℤ) (ν' : ℕ → ℤ),
      σ = S i (Ti, p, (x.tr + q : ℕ), a, b, c) ν' ∧
      TrieMem ν' x.tr x.cap x.fp (child Ti q) ∧ SameOutsideTrie μ ν' x.tr x.cap x.fp)
      ?_ ?_ (by decide)
    · refine Ends.iteLast (fun hz => ?_) (fun hnz => ?_) (by light_side)
      · have hz' : Ti.getD q 0 = 0 := by simpa [hptr] using hz
        have hfree := hmem.free
        obtain ⟨hset, hkept⟩ := hmem.set hq (Ti.length : ℤ)
        obtain ⟨hnew, hkept'⟩ := hset.new (by simp; omega)
        simp only [List.length_set] at hnew hkept'
        light_steps using hfree, S
        refine Ends.next _ (Ends.clearLoop hs (a := x.tr + Ti.length) (n := 11) (by decide) rfl rfl
          (by omega) ?_ (hT := le_rfl))
        rw [update_frame_setLocal]
        light_step
        exact ⟨_, _, _, _, rfl, by rwa [child, ite_eq_left hz'], hsame.trans (hkept.trans hkept')⟩
      · have hz' : Ti.getD q 0 ≠ 0 := by simpa [hptr] using hnz
        light_skip
        exact ⟨_, _, _, _, rfl, by rwa [child, ite_eq_right hz'], hsame⟩
    · rintro _ ⟨a, b, c, ν', rfl, hc, hkeep⟩
      have hq' : q < (child Ti q).length := by grind
      have hread := hc.seg.getD hq' 0
      have hcap := hc.le_cap
      generalize (child Ti q).getD q 0 = val at hchild hnext hread
      light_set (val.toNat : ℕ) using hread, S
      exact ⟨(child Ti q, val.toNat, _, a, b, c), ν', rfl, hnext, hc, hkeep⟩
  · dsimp only [I]
    rintro ⟨Ti, p, a, b, c, e⟩ ν ⟨hprog, hmem, hsame⟩
    dsimp at hprog hmem
    have hin := hprog.inside
    have hle := hmem.le_cap
    obtain ⟨hset, hkeep⟩ := hmem.set (q := p) (by omega) x.val
    have heq := hprog.eq
    rw [List.drop_length, trieInsert] at heq
    light_step using S
    exact ⟨heq ▸ hset, hsame.trans hkeep⟩
  · rw [update_frame_setLocal, ← frame_append_zeros _ 4]
    rfl

end Light.Sec4
