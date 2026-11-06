/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Induction
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# Tries in one array (Section 4.3)

"for each tile we store its boxes, with their values, in a standard trie on their strings of L
symbols.  Thus […] looking up or inserting a box, takes O(L) operations."  Here a string is a list
of L digits below 11, for the ten terms and the star.

All tries live in one array of integers and are numbered; the number of a trie is the number of its
tile.  A vertex is a block of eleven consecutive cells, one for each symbol, holding the address of
the child, or 0 if there is none; a vertex at depth L holds the value of its box in its first cell.
A box is stored if the pointers for its L symbols lead from the root of the trie to such a vertex
(`trieWalk`).  A new vertex is appended at the end of the array (`trieNew`).  The two operations
are `trieInsert` and `trieLookup`.

The interface is `TrieRep`: "the array holds tries with these roots and these stored values".  It
holds for an array without tries (`TrieRep.empty`), it is kept by a new trie (`TrieRep.new`) and by
an insertion (`TrieRep.insert`), and it says what a lookup returns (`TrieRep.lookup`).  `WalkOK` and
`InsertOK` say in addition that every address met on the way lies inside the array
(`TrieRep.walkOK`, `TrieRep.insertOK`).

The proof.  The pair (i, w) names the vertex of trie number i to which the prefix w leads.  The
invariant `TrieInv` gives every vertex its address nd (i, w), 0 if there is none.  `TrieRep` says
that such an nd exists, with nd (i, []) = roots i and the value v in the cell nd x for every entry
f x = some v.
1. Three steps keep the invariant: a new root, a new child, a value written at depth L
   (`TrieInv.newRoot`, `TrieInv.newChild`, `TrieInv.setVal`).  The first gives `TrieRep.new`.
2. An insertion is a sequence of new children and then one write.  Each step extends the tries
   (`TrieExt`): no vertex moves, no root appears, no value of another string changes.  `Inserted`
   collects what holds at the end, and `trieInsert_spec` proves it by induction on the rest of the
   string.  This gives `TrieRep.insert` and `TrieRep.insertOK`.
3. A lookup goes from the vertex of a prefix to the vertex of the next prefix (`trieWalk_spec`).
   This gives `TrieRep.lookup` and `TrieRep.walkOK`.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The operations -/

/-- The vertex reached from the vertex p by following the symbols of a string. -/
def trieWalk (T : List ℤ) p
  | [] => p
  | d :: l => trieWalk T (T.getD (p + d) 0).toNat l

/-- The value stored for a string in the trie with the given root (for a string that is stored; see
`TrieRep.lookup`). -/
def trieLookup (T : List ℤ) root key := T.getD (trieWalk T root key) 0

/-- The array with a new vertex (without children) at its end; its address is the old length. -/
def trieNew (T : List ℤ) := T ++ List.replicate 11 0

/-- The array after storing the value v for a string, starting from the vertex p. -/
def trieInsert (T : List ℤ) p
  | [], v => T.set p v
  | d :: l, v =>
    if T.getD (p + d) 0 = 0 then trieInsert (trieNew (T.set (p + d) T.length)) T.length l v
    else trieInsert T (T.getD (p + d) 0).toNat l v

/-- Following a string from the vertex p, every vertex met is inside the array and every pointer
read is positive. -/
def WalkOK (T : List ℤ) p
  | [] => 0 < p ∧ p + 11 ≤ T.length
  | d :: l => 0 < p ∧ p + 11 ≤ T.length ∧ 0 < T.getD (p + d) 0 ∧ WalkOK T (T.getD (p + d) 0).toNat l

/-- An insertion of a string from the vertex p follows the array as it changes: every vertex met is
inside the array, and every pointer read is 0 or positive. -/
def InsertOK (T : List ℤ) p
  | [] => 0 < p ∧ p + 11 ≤ T.length
  | d :: l => 0 < p ∧ p + 11 ≤ T.length ∧
      if T.getD (p + d) 0 = 0 then InsertOK (trieNew (T.set (p + d) T.length)) T.length l
      else 0 < T.getD (p + d) 0 ∧ InsertOK T (T.getD (p + d) 0).toNat l

/-- A vertex has eleven cells. -/
theorem length_trieNew T : (trieNew T).length = T.length + 11 := by
  simp [trieNew]

/-- An insertion adds at most one vertex for each symbol (proof of Lemma 29: "adds at most L
vertices per box"). -/
theorem length_trieInsert_le T p key v :
    (trieInsert T p key v).length ≤ T.length + 11 * key.length := by
  induction key generalizing T p with
  | nil => simp [trieInsert]
  | cons d l ih =>
    grind [length_trieNew, trieInsert]

end ThreeSumApsp.Spec

end

namespace ThreeSumApsp.Spec

/-! ## Arrays as functions -/

/-- The cells of an array, as a function; beyond the end of the array it is 0. -/
def cells (T : List ℤ) := fun a => T.getD a 0

private theorem cells_set T a z (ha : a < T.length) :
    cells (T.set a z) = Function.update (cells T) a z := by
  funext x
  by_cases hx : x = a
  · subst hx
    simp [cells, ha]
  · grind [cells]

private theorem cells_trieNew T : cells (trieNew T) = cells T := by
  grind [cells, trieNew]

private theorem cells_of_le T a (ha : T.length ≤ a) : cells T a = 0 := by
  simp_all [cells]

/-! ## The invariant -/

/-- The cells μ hold tries for strings of length L.  The pair (i, w) names the vertex of trie number
i for the prefix w, and nd (i, w) is its address, or 0 if there is no such vertex.  The vertices are
blocks of eleven cells in the region from lo to fr, the first free cell. -/
structure TrieInv (L lo : ℕ) (μ : Light.Memory) (nd : ℕ × List ℕ → ℕ) (fr : ℕ) : Prop where
  /-- The cell number a of a vertex above depth L points to the child for the symbol a. -/
  child : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 → μ (nd (i, w) + a) = nd (i, w ++ [a])
  /-- The vertices are aligned blocks between lo and fr. -/
  range : ∀ x, nd x ≠ 0 → lo ≤ nd x ∧ nd x + 11 ≤ fr ∧ 11 ∣ nd x - lo
  /-- Different prefixes have different vertices. -/
  inj : ∀ x y, nd x ≠ 0 → nd x = nd y → x = y
  /-- The parent of a vertex is a vertex. -/
  closed : ∀ i w a, nd (i, w ++ [a]) ≠ 0 → nd (i, w) ≠ 0
  /-- The cells from fr on are free. -/
  fresh : ∀ a, fr ≤ a → μ a = 0
  /-- The address 0 means: no vertex. -/
  lo_pos : 0 < lo
  /-- The free region starts at a block boundary. -/
  fr_aligned : lo ≤ fr ∧ 11 ∣ fr - lo

namespace TrieInv

variable {L lo fr : ℕ} {μ : Light.Memory} {nd : ℕ × List ℕ → ℕ}

variable (h : TrieInv L lo μ nd fr)

include h in
/-- A vertex lies below the first free cell, and its address is not 0. -/
private theorem inside {x} (hx : nd x ≠ 0) :
    0 < nd x ∧ nd x + 11 ≤ fr :=
  ⟨Nat.pos_of_ne_zero hx, (h.range x hx).2.1⟩

include h in
/-- The blocks of different vertices are disjoint. -/
private theorem cell_inj {x y} {a b} (hx : nd x ≠ 0)
    (hy : nd y ≠ 0) (ha : a < 11) (hb : b < 11) (hcell : nd x + b = nd y + a) :
    x = y ∧ b = a := by
  have  := h.range x hx
  have  := h.range y hy
  -- both addresses are lo plus a multiple of 11, and a, b < 11
  exact ⟨h.inj x y hx (by omega), by omega⟩

/-- The prefixes of a prefix that has a vertex have vertices. -/
private def prefix_ne (h : TrieInv L lo μ nd fr) {i} {w} l
    (hw : nd (i, w ++ l) ≠ 0) := by
  induction l using List.reverseRecOn with
  | nil => simpa using hw
  | append_singleton l a ih =>
    rw [← List.append_assoc] at hw
    exact ih (h.closed _ _ _ hw)

include h in
/-- A new vertex x at the address fr; its parent, if x is not a root, is a vertex already.  The
cells may change, as long as those from fr on stay free and the cells of the old vertices point to
the children, x among them. -/
private theorem addVertex {x} {μ' : Light.Memory} (hx : nd x = 0)
    (hparent : ∀ i w a, (i, w ++ [a]) = x → nd (i, w) ≠ 0) (hfresh : ∀ c, fr ≤ c → μ' c = 0)
    (hchild : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 →
      μ' (nd (i, w) + a) = Function.update nd x fr (i, w ++ [a])) :
    TrieInv L lo μ' (Function.update nd x fr) (fr + 11) := by
  have hlo := h.lo_pos
  have  := h.fr_aligned
  refine { child := fun i w a hw ha hnd => ?_, range := fun y hnd => ?_,
           inj := fun y y' hnd heq => ?_, closed := fun i w a hnd => ?_,
           fresh := fun c hc => hfresh c (by omega), lo_pos := hlo,
           fr_aligned := ⟨by omega, by omega⟩ }
  · -- child
    by_cases hwx : (i, w) = x
    · -- the new vertex has no children
      have  : (i, w ++ [a]) ≠ x := fun happ => by simp [← hwx] at happ
      have  : nd (i, w ++ [a]) = 0 := by
        by_contra hc
        exact h.closed _ _ _ hc (by rw [hwx, hx])
      simp_all
    · simp_all
  · -- range
    rw [Function.update_apply] at hnd ⊢
    split_ifs at hnd ⊢
    · omega
    · have := h.range y hnd
      omega
  · -- inj: the new address is above all the old ones
    rw [Function.update_apply] at hnd
    rw [Function.update_apply, Function.update_apply] at heq
    split_ifs at hnd heq with hyx hyx'
    · rw [hyx, hyx']
    · have := h.range y' (by omega)
      omega
    · have := h.range y hnd
      omega
    · exact h.inj y y' hnd heq
  · -- closed
    by_cases hwx : (i, w) = x
    · grind
    · rw [Function.update_of_ne hwx]
      by_cases happ : (i, w ++ [a]) = x
      · exact hparent i w a happ
      · exact h.closed i w a (by simp_all)

/-- A new trie number i: its root is a new vertex at the address fr. -/
private def newRoot (h : TrieInv L lo μ nd fr) i (hi : nd (i, []) = 0) := by
  have hne : ∀ j w (a : ℕ), (j, w ++ [a]) ≠ (i, []) := fun j w a happ => by
    simp at happ
  refine h.addVertex hi (fun j w a happ => absurd happ (hne j w a)) h.fresh
    fun j w a hw ha hnd => ?_
  rw [Function.update_of_ne (hne j w a), h.child j w a hw ha hnd]

include h in
/-- A new vertex for the prefix w ++ [a], at the address fr, with the pointer to it in the vertex
of w. -/
private theorem newChild {i} {w} {a} (ha : a < 11)
    (hw : nd (i, w) ≠ 0) (hwa : nd (i, w ++ [a]) = 0) :
    TrieInv L lo (Function.update μ (nd (i, w) + a) fr) (Function.update nd (i, w ++ [a]) fr)
      (fr + 11) := by
  have  := h.inside hw
  refine h.addVertex hwa (fun j u b happ => ?_) (fun c hc => ?_) fun j u b hu hb hnd => ?_
  · simp_all
  · rw [Function.update_of_ne (by omega), h.fresh c hc]
  · by_cases hcell : nd (j, u) + b = nd (i, w) + a
    · obtain ⟨hju, rfl⟩ := h.cell_inj hnd hw ha hb hcell
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hju
      rw [Function.update_self, Function.update_self]
    · have hne : (j, u ++ [b]) ≠ (i, w ++ [a]) := fun happ => by
        simp_all
      rw [Function.update_of_ne hcell, Function.update_of_ne hne, h.child j u b hu hb hnd]

include h in
/-- Writing a value into the vertex of a string of full length. -/
private theorem setVal {i} {w} (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) z : TrieInv L lo (Function.update μ (nd (i, w)) z) nd fr := by
  have  := h.inside hw
  refine { h with child := fun j u b hu hb hnd => ?_, fresh := fun c hc => ?_ }
  · rw [Function.update_of_ne, h.child j u b hu hb hnd]
    intro hcell
    obtain ⟨hju, -⟩ := h.cell_inj (a := 0) hnd hw (by omega) hb hcell
    obtain ⟨-, rfl⟩ := Prod.mk.inj hju
    -- a vertex at depth L is not above depth L
    omega
  · rw [Function.update_of_ne (by omega), h.fresh c hc]

end TrieInv

/-! ## Insertion -/

/-- The tries (μ', nd') extend the tries (μ, nd): no vertex moves, there is no new root, and the
value of every string other than x is kept. -/
private structure TrieExt (L : ℕ) (x : ℕ × List ℕ) (μ : Light.Memory) (nd : ℕ × List ℕ → ℕ) (μ' : Light.Memory)
    (nd' : ℕ × List ℕ → ℕ) : Prop where
  old_vertex : ∀ y, nd y ≠ 0 → nd' y = nd y
  old_root : ∀ i, nd' (i, []) ≠ 0 → nd (i, []) ≠ 0
  old_value : ∀ i w, w.length = L → nd (i, w) ≠ 0 → (i, w) ≠ x → μ' (nd (i, w)) = μ (nd (i, w))

private theorem TrieExt.trans {L} {x} {μ μ₁ μ₂}
    {nd nd₁ nd₂} (h : TrieExt L x μ nd μ₁ nd₁) (h' : TrieExt L x μ₁ nd₁ μ₂ nd₂) :
    TrieExt L x μ nd μ₂ nd₂ := by

  refine { old_vertex := fun y hy => ?_, old_root := fun i hi => h.old_root i (h'.old_root i hi),
           old_value := fun i w hL hw hx => ?_ }
  · ram_arith
  · ram_safe

/-- T' with the vertices nd' is T with the vertices nd after the value v was stored for the string
x: the invariant holds, x has a vertex, the vertex holds v, and the tries have been extended. -/
private structure Inserted (L lo : ℕ) (x : ℕ × List ℕ) (v : ℤ) (T : List ℤ) (nd : ℕ × List ℕ → ℕ)
    (T' : List ℤ) (nd' : ℕ × List ℕ → ℕ) : Prop where
  inv : TrieInv L lo (cells T') nd' T'.length
  vertex : nd' x ≠ 0
  value : cells T' (nd' x) = v
  ext : TrieExt L x (cells T) nd (cells T') nd'

/-- An insertion after a step that extends the tries. -/
private def Inserted.of_step {L lo} {x} {v} {T T₁ T₂}
    {nd nd₁ nd₂} (h : Inserted L lo x v T₁ nd₁ T₂ nd₂)
    (hstep : TrieExt L x (cells T) nd (cells T₁) nd₁) :=
  { h with ext := hstep.trans h.ext }

section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}

variable (h : TrieInv L lo (cells T) nd T.length)

include h in
/-- The end of an insertion: the value is written into the vertex of the string. -/
private theorem TrieInv.inserted_set  (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) v : Inserted L lo (i, w) v T nd (T.set (nd (i, w)) v) nd := by
  have  := h.inside hw
  have hcells : cells (T.set (nd (i, w)) v) = Function.update (cells T) (nd (i, w)) v :=
    cells_set T _ _ (by omega)
  refine { inv := ?_, vertex := hw, value := ?_,
           ext := { old_vertex := fun _ _ => rfl, old_root := fun _ hi => hi,
                    old_value := fun j u _ hu hne => ?_ } }
  · rw [hcells, List.length_set]
    exact h.setVal hL hw v
  · simp_all
  · rw [hcells, Function.update_of_ne fun hnd => hne (h.inj _ _ hu hnd)]

include h in
/-- A step of an insertion where there is no child: a new vertex at the end of the array keeps the
invariant and extends the tries. -/
private theorem TrieInv.step_newChild  {d}
    (hd : d < 11) (hw : nd (i, w) ≠ 0) (hlen : w.length < L) (hnone : nd (i, w ++ [d]) = 0)
     x :
    TrieInv L lo (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length)
        (trieNew (T.set (nd (i, w) + d) T.length)).length ∧
      TrieExt L x (cells T) nd (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length) := by
  have  := h.inside hw
  rw [cells_trieNew, cells_set T _ _ (by omega), length_trieNew, List.length_set]
  refine ⟨h.newChild hd hw hnone,
    { old_vertex := fun y hy => ?_, old_root := fun j hj => ?_,
      old_value := fun j u hL hu _ => ?_ }⟩
  · grind
  · simp_all
  · refine Function.update_of_ne (fun hcell => ?_) _ _
    obtain ⟨hju, -⟩ := h.cell_inj (b := 0) hu hw hd (by omega) hcell
    simp_all

/-- **Insertion.**  Below the vertex of the prefix w, the insertion of the rest of a string meets
only addresses inside the array, and it achieves what `Inserted` says. -/
private theorem trieInsert_spec v key (hinv : TrieInv L lo (cells T) nd T.length)
    (hw : nd (i, w) ≠ 0) (hlen : w.length + key.length = L) (hkey : ∀ d ∈ key, d < 11) :
    InsertOK T (nd (i, w)) key ∧
      ∃ nd', Inserted L lo (i, w ++ key) v T nd (trieInsert T (nd (i, w)) key v) nd' := by
  induction key generalizing T nd w with
  | nil =>
    rw [List.append_nil]
    exact ⟨hinv.inside hw, nd, hinv.inserted_set hlen hw v⟩
  | cons d l ih =>
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    have hd := hkey d (by simp)
    have hl : ∀ x ∈ l, x < 11 := fun x hx => hkey x (by simp [hx])
    rw [List.length_cons] at hlen
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) := hinv.child i w d (by omega) hd hw
    have hlen' : (w ++ [d]).length + l.length = L := by
      grind
    rw [List.append_cons, trieInsert, InsertOK, hchild]
    by_cases hz : nd (i, w ++ [d]) = 0
    · -- there is no child: a new vertex at the end of the array
      obtain ⟨hinv₁, hstep⟩ := hinv.step_newChild hd hw (by omega) hz (i, w ++ [d] ++ l)
      obtain ⟨hok, nd', hins⟩ :=
        ih hinv₁ (by grind) hlen' hl
      rw [Function.update_self] at hok hins
      rw [hz, Int.natCast_zero, if_pos rfl, if_pos rfl]
      exact ⟨⟨hpos, hin, hok⟩, nd', hins.of_step hstep⟩
    · -- the child exists
      obtain ⟨hok, nd', hins⟩ := ih hinv hz hlen' hl
      have hz' : (nd (i, w ++ [d]) : ℤ) ≠ 0 := mod_cast hz
      rw [if_neg hz', if_neg hz', Int.toNat_natCast]
      exact ⟨⟨hpos, hin, by omega, hok⟩, nd', hins⟩

/-! ## Lookup -/

/-- **Lookup.**  Following the symbols of a string whose vertex exists leads to that vertex, through
addresses inside the array. -/
private theorem trieWalk_spec (hinv : TrieInv L lo (cells T) nd T.length) key
    (hlen : w.length + key.length ≤ L) (hkey : ∀ d ∈ key, d < 11) (hne : nd (i, w ++ key) ≠ 0) :
    WalkOK T (nd (i, w)) key ∧ trieWalk T (nd (i, w)) key = nd (i, w ++ key) := by
  induction key generalizing w with
  | nil =>
    rw [List.append_nil] at hne ⊢
    exact ⟨hinv.inside hne, rfl⟩
  | cons d l ih =>
    rw [List.length_cons] at hlen
    rw [List.append_cons] at hne ⊢
    have hwd := hinv.prefix_ne l hne
    have hw := hinv.prefix_ne [d] hwd
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) :=
      hinv.child i w d (by omega) (hkey d (by simp)) hw
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    obtain ⟨hok, hwalk⟩ := ih
      (by grind)
      (fun x hx => hkey x (by simp [hx])) hne
    rw [WalkOK, trieWalk, hchild, Int.toNat_natCast]
    exact ⟨⟨hpos, hin, by omega, hok⟩, hwalk⟩

end

/-! ## The interface -/

public section

/-- The array T holds, from the address lo on, tries number 0, 1, … for strings of L symbols.  The
root of trie number i is at the address roots i (0 if the trie does not exist yet), and every entry
f (i, key) = some v is stored: the string key has the value v in trie number i.  The array may hold
more than f lists. -/
def TrieRep L lo T (roots : ℕ → ℕ) (f : ℕ × List ℕ → Option ℤ) :=
  ∃ nd, TrieInv L lo (cells T) nd T.length ∧ (∀ i, nd (i, []) = roots i) ∧
    ∀ i key v, f (i, key) = some v → key.length = L ∧ nd (i, key) ≠ 0 ∧ cells T (nd (i, key)) = v

namespace TrieRep

/-- An array without tries: any array of positive length.  The tries will be built behind it: lo is
its length. -/
theorem empty L T (hT : 0 < T.length) :
    TrieRep L T.length T (fun _ => 0) fun _ => none :=
  -- no prefix has a vertex, so the fields on vertices hold vacuously
  ⟨fun _ => 0,
    { child := fun _ _ _ _ _ h => absurd rfl h, range := fun _ h => absurd rfl h,
      inj := fun _ _ h => absurd rfl h, closed := fun _ _ _ h => absurd rfl h,
      fresh := fun a ha => cells_of_le T a ha, lo_pos := hT,
      fr_aligned := ⟨Nat.le_refl _, by simp⟩ },
    fun _ => rfl, fun _ _ _ h => by simp at h⟩

variable {L lo : ℕ} {T : List ℤ} {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}

variable (h : TrieRep L lo T roots f)

include h in
/-- The array is not empty: the address 0 means that there is no vertex. -/
theorem length_pos  : 0 < T.length := by
  obtain ⟨nd, hinv, -, -⟩ := h
  exact Nat.lt_of_lt_of_le hinv.lo_pos hinv.fr_aligned.1

/-- Fewer stored values are a weaker claim. -/
theorem mono {g} (h : TrieRep L lo T roots f)
    (hg : ∀ x v, g x = some v → f x = some v) : TrieRep L lo T roots g := by
  ram_safe [ThreeSumApsp.Spec.TrieRep]

include h in
/-- A new, empty trie number i. -/
theorem new  i (hi : roots i = 0) :
    TrieRep L lo (trieNew T) (Function.update roots i T.length) f := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  refine ⟨Function.update nd (i, []) T.length, ?_, fun j => ?_, fun j key v hf => ?_⟩
  · rw [cells_trieNew, length_trieNew]
    exact hinv.newRoot i (by rw [hroots, hi])
  · grind
  · obtain ⟨hlen, hne, hv⟩ := hval j key v hf
    rw [Function.update_of_ne fun hkey => hne (by rw [hkey, hroots, hi]), cells_trieNew]
    exact ⟨hlen, hne, hv⟩

/-- What `trieInsert_spec` says about an insertion from the root of trie number i. -/
private def insert_spec nd (hinv : TrieInv L lo (cells T) nd T.length)
    (hroots : ∀ i, nd (i, []) = roots i) i hi (key : List ℕ)
    (hk : key.length = L) hd v := by
  have h := trieInsert_spec (i := i) (w := []) v key hinv (by rwa [hroots]) (by simpa using hk) hd
  rwa [hroots] at h

include h in
/-- Storing a value. -/
theorem insert  i (hi : roots i ≠ 0) key
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) v :
    TrieRep L lo (trieInsert T (roots i) key v) roots (Function.update f (i, key) (some v)) := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  obtain ⟨-, nd', hins⟩ := insert_spec nd hinv hroots i hi key hk hd v
  refine ⟨nd', hins.inv, fun j => ?_, fun j key' v' hf => ?_⟩
  · by_cases hz : roots j = 0
    · -- a trie that does not exist still does not exist
      by_contra hc
      exact hins.ext.old_root j (fun hnd => hc (by rw [hnd, hz])) (by rw [hroots, hz])
    · rw [hins.ext.old_vertex (j, []) (by rwa [hroots]), hroots]
  · by_cases hkey : (j, key') = (i, key)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
      rw [Function.update_self] at hf
      obtain rfl := Option.some.inj hf
      exact ⟨hk, hins.vertex, hins.value⟩
    · rw [Function.update_of_ne hkey] at hf
      obtain ⟨hlen, hne, hv⟩ := hval j key' v' hf
      rw [hins.ext.old_vertex _ hne]
      exact ⟨hlen, hne, (hins.ext.old_value j key' hlen hne hkey).trans hv⟩

include h in
/-- During an insertion, every cell read holds 0 or the address of a vertex inside the array. -/
theorem insertOK  i (hi : roots i ≠ 0) key
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) : InsertOK T (roots i) key := by
  obtain ⟨nd, hinv, hroots, -⟩ := h
  exact (insert_spec nd hinv hroots i hi key hk hd 0).1

include h in
/-- What `trieWalk_spec` says about the way from the root of trie number i down a stored string. -/
private theorem walk_spec  i key
    (hd : ∀ d ∈ key, d < 11) v (hf : f (i, key) = some v) :
    WalkOK T (roots i) key ∧ T.getD (trieWalk T (roots i) key) 0 = v := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  obtain ⟨hlen, hne, hv⟩ := hval i key v hf
  obtain ⟨hok, hwalk⟩ := trieWalk_spec (w := []) hinv key (by simp [hlen]) hd hne
  rw [hroots] at hok hwalk
  exact ⟨hok, by rw [hwalk]; exact hv⟩

/-- Looking up a stored value. -/
def lookup (h : TrieRep L lo T roots f) i key hd v
     hf :=
  (h.walk_spec i key hd v hf).2

/-- On the way down a stored string, every cell read holds the address of a vertex inside the
array. -/
def walkOK (h : TrieRep L lo T roots f) i key hd v
     hf :=
  (h.walk_spec i key hd v hf).1

end TrieRep

end

end ThreeSumApsp.Spec
