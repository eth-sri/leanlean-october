/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

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
A new root or child keeps the invariant and preserves all previously stored entries.
Insertion applies the child rule until it reaches the leaf, where it updates just that entry.
Lookup follows the prefixes of the stored string.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The operations -/

/-- The vertex reached from the vertex p by following the symbols of a string. -/
def trieWalk (T : List ℤ) (p : ℕ) : List ℕ → ℕ
  | [] => p
  | d :: l => trieWalk T (T.getD (p + d) 0).toNat l

/-- The value stored for a string in the trie with the given root (for a string that is stored; see
`TrieRep.lookup`). -/
def trieLookup (T : List ℤ) (root : ℕ) (key : List ℕ) : ℤ := T.getD (trieWalk T root key) 0

/-- The array with a new vertex (without children) at its end; its address is the old length. -/
def trieNew (T : List ℤ) : List ℤ := T ++ List.replicate 11 0

/-- The array after storing the value v for a string, starting from the vertex p. -/
def trieInsert (T : List ℤ) (p : ℕ) : List ℕ → ℤ → List ℤ
  | [], v => T.set p v
  | d :: l, v =>
    if T.getD (p + d) 0 = 0 then trieInsert (trieNew (T.set (p + d) T.length)) T.length l v
    else trieInsert T (T.getD (p + d) 0).toNat l v

/-- Following a string from the vertex p, every vertex met is inside the array and every pointer
read is positive. -/
def WalkOK (T : List ℤ) (p : ℕ) : List ℕ → Prop
  | [] => 0 < p ∧ p + 11 ≤ T.length
  | d :: l => 0 < p ∧ p + 11 ≤ T.length ∧ 0 < T.getD (p + d) 0 ∧ WalkOK T (T.getD (p + d) 0).toNat l

/-- An insertion of a string from the vertex p follows the array as it changes: every vertex met is
inside the array, and every pointer read is 0 or positive. -/
def InsertOK (T : List ℤ) (p : ℕ) : List ℕ → Prop
  | [] => 0 < p ∧ p + 11 ≤ T.length
  | d :: l => 0 < p ∧ p + 11 ≤ T.length ∧
      if T.getD (p + d) 0 = 0 then InsertOK (trieNew (T.set (p + d) T.length)) T.length l
      else 0 < T.getD (p + d) 0 ∧ InsertOK T (T.getD (p + d) 0).toNat l

/-- A vertex has eleven cells. -/
theorem length_trieNew (T : List ℤ) : (trieNew T).length = T.length + 11 := by
  simp [trieNew]

/-- An insertion adds at most one vertex for each symbol (proof of Lemma 29: "adds at most L
vertices per box"). -/
theorem length_trieInsert_le (T : List ℤ) (p : ℕ) (key : List ℕ) (v : ℤ) :
    (trieInsert T p key v).length ≤ T.length + 11 * key.length := by
  induction key generalizing T p <;> grind [trieInsert, trieNew, length_trieNew]

end ThreeSumApsp.Spec

end

namespace ThreeSumApsp.Spec

/-! ## Arrays as functions -/

/-- The cells of an array, as a function; beyond the end of the array it is 0. -/
def cells (T : List ℤ) : ℕ → ℤ := fun a => T.getD a 0

private theorem cells_set (T : List ℤ) (a : ℕ) (z : ℤ) (ha : a < T.length) :
    cells (T.set a z) = Function.update (cells T) a z := by
  grind [cells]

private theorem cells_trieNew (T : List ℤ) : cells (trieNew T) = cells T := by
  grind [cells, trieNew]

/-! ## The invariant -/

/-- The cells μ hold tries for strings of length L.  The pair (i, w) names the vertex of trie number
i for the prefix w, and nd (i, w) is its address, or 0 if there is no such vertex.  The vertices are
blocks of eleven cells in the region from lo to fr, the first free cell. -/
structure TrieInv (L lo : ℕ) (μ : ℕ → ℤ) (nd : ℕ × List ℕ → ℕ) (fr : ℕ) : Prop where
  /-- The cell number a of a vertex above depth L points to the child for the symbol a. -/
  child : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 → μ (nd (i, w) + a) = nd (i, w ++ [a])
  /-- The vertices are aligned blocks between lo and fr. -/
  range : ∀ x, nd x ≠ 0 → lo ≤ nd x ∧ nd x + 11 ≤ fr ∧ 11 ∣ (nd x - lo)
  /-- Different prefixes have different vertices. -/
  inj : ∀ x y, nd x ≠ 0 → nd x = nd y → x = y
  /-- The parent of a vertex is a vertex. -/
  closed : ∀ i w a, nd (i, w ++ [a]) ≠ 0 → nd (i, w) ≠ 0
  /-- The cells from fr on are free. -/
  fresh : ∀ a, fr ≤ a → μ a = 0
  /-- The address 0 means: no vertex. -/
  lo_pos : 0 < lo
  /-- The free region starts at a block boundary. -/
  fr_aligned : lo ≤ fr ∧ 11 ∣ (fr - lo)

namespace TrieInv

variable {L lo fr : ℕ} {μ : ℕ → ℤ} {nd : ℕ × List ℕ → ℕ}

/-- A vertex lies below the first free cell, and its address is not 0. -/
private theorem inside (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} (hx : nd x ≠ 0) :
    0 < nd x ∧ nd x + 11 ≤ fr :=
  ⟨Nat.pos_of_ne_zero hx, (h.range x hx).2.1⟩

/-- The blocks of different vertices are disjoint. -/
private theorem cell_inj (h : TrieInv L lo μ nd fr) {x y : ℕ × List ℕ} {a b : ℕ} (hx : nd x ≠ 0)
    (hy : nd y ≠ 0) (ha : a < 11) (hb : b < 11) (hcell : nd x + b = nd y + a) :
    x = y ∧ b = a := by
  have hrx := h.range x hx
  have hry := h.range y hy
  -- both addresses are lo plus a multiple of 11, and a, b < 11
  exact ⟨h.inj x y hx (by omega), by omega⟩

/-- The prefixes of a prefix that has a vertex have vertices. -/
private theorem prefix_ne (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (l : List ℕ)
    (hw : nd (i, w ++ l) ≠ 0) : nd (i, w) ≠ 0 := by
  induction l using List.reverseRecOn with
  | nil => simp_all
  | append_singleton l a ih =>
    rw [← List.append_assoc] at hw
    exact ih (h.closed _ _ _ hw)

/-- A new vertex x at the address fr; its parent, if x is not a root, is a vertex already.  The
cells may change, as long as those from fr on stay free and the cells of the old vertices point to
the children, x among them. -/
private theorem addVertex (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} {μ' : ℕ → ℤ} (hx : nd x = 0)
    (hparent : ∀ i w a, (i, w ++ [a]) = x → nd (i, w) ≠ 0) (hfresh : ∀ c, fr ≤ c → μ' c = 0)
    (hchild : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 →
      μ' (nd (i, w) + a) = Function.update nd x fr (i, w ++ [a])) :
    TrieInv L lo μ' (Function.update nd x fr) (fr + 11) := by
  have hlo := h.lo_pos
  have hfr := h.fr_aligned
  refine { child := fun i w a hw ha hnd => ?_, range := fun y hnd => ?_,
           inj := fun y y' hnd heq => ?_, closed := fun i w a hnd => ?_,
           fresh := fun c hc => hfresh c (by omega), lo_pos := hlo,
           fr_aligned := ⟨by omega, by omega⟩ }
  · -- child
    by_cases hwx : (i, w) = x
    · -- the new vertex has no children
      have hne : (i, w ++ [a]) ≠ x := fun happ => by grind
      have hnone : nd (i, w ++ [a]) = 0 := by
        by_contra hc
        exact h.closed _ _ _ hc (by simp_all)
      simp_all
    simp_all
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
    · simp_all
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
      · grind
      · exact h.closed i w a (by simp_all)

/-- A new trie number i: its root is a new vertex at the address fr. -/
private theorem newRoot (h : TrieInv L lo μ nd fr) (i : ℕ) (hi : nd (i, []) = 0) :
    TrieInv L lo μ (Function.update nd (i, []) fr) (fr + 11) := by
  have hne : ∀ (j : ℕ) (w : List ℕ) (a : ℕ), (j, w ++ [a]) ≠ (i, []) := fun j w a happ => by
    simp_all
  refine h.addVertex hi (fun j w a happ => absurd happ (hne j w a)) h.fresh
    fun j w a hw ha hnd => ?_
  rw [Function.update_of_ne (hne j w a), h.child j w a hw ha hnd]

/-- A new vertex for the prefix w ++ [a], at the address fr, with the pointer to it in the vertex
of w. -/
private theorem newChild (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} {a : ℕ} (ha : a < 11)
    (hw : nd (i, w) ≠ 0) (hwa : nd (i, w ++ [a]) = 0) :
    TrieInv L lo (Function.update μ (nd (i, w) + a) fr) (Function.update nd (i, w ++ [a]) fr)
      (fr + 11) := by
  have hin := h.inside hw
  refine h.addVertex hwa (fun j u b happ => ?_) (fun c hc => ?_) fun j u b hu hb hnd => ?_
  · simp_all
  · rw [Function.update_of_ne (by omega), h.fresh c hc]
  · by_cases hcell : nd (j, u) + b = nd (i, w) + a
    · obtain ⟨hju, rfl⟩ := h.cell_inj hnd hw ha hb hcell
      simp_all
    · have hne : (j, u ++ [b]) ≠ (i, w ++ [a]) := fun happ => by
        simp_all
      rw [Function.update_of_ne hcell, Function.update_of_ne hne, h.child j u b hu hb hnd]

/-- Writing a value into the vertex of a string of full length. -/
private theorem setVal (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (z : ℤ) : TrieInv L lo (Function.update μ (nd (i, w)) z) nd fr := by
  have hin := h.inside hw
  refine { h with child := fun j u b hu hb hnd => ?_, fresh := fun c hc => ?_ }
  · rw [Function.update_of_ne, h.child j u b hu hb hnd]
    intro hcell
    obtain ⟨hju, -⟩ := h.cell_inj (a := 0) hnd hw (by omega) hb hcell
    simp_all
  · rw [Function.update_of_ne (by omega), h.fresh c hc]

end TrieInv

/-! ## The representation and insertion -/

private structure TrieState (L lo : ℕ) (T : List ℤ) (roots : ℕ → ℕ)
    (f : ℕ × List ℕ → Option ℤ) (nd : ℕ × List ℕ → ℕ) : Prop where
  inv : TrieInv L lo (cells T) nd T.length
  root : ∀ i, nd (i, []) = roots i
  value : ∀ x v, f x = some v → x.2.length = L ∧ nd x ≠ 0 ∧ cells T (nd x) = v

section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}
  {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}

private theorem TrieState.write (h : TrieState L lo T roots f nd) (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (v : ℤ) :
    TrieState L lo (T.set (nd (i, w)) v) roots (Function.update f (i, w) (some v)) nd := by
  have hin := h.inv.inside hw
  have hc := cells_set T (nd (i, w)) v (by omega)
  refine ⟨by simpa only [hc, List.length_set] using h.inv.setVal hL hw v, h.root, fun x z hz => ?_⟩
  rw [hc]
  by_cases hx : x = (i, w)
  · subst x; simp_all
  · rw [Function.update_of_ne hx] at hz
    obtain ⟨hL, hne, hv⟩ := h.value x z hz
    rw [Function.update_of_ne fun he => hx (h.inv.inj _ _ hne he)]
    exact ⟨hL, hne, hv⟩

private theorem TrieState.addChild (h : TrieState L lo T roots f nd) {a : ℕ}
    (ha : a < 11) (hw : nd (i, w) ≠ 0) (hL : w.length < L) (hz : nd (i, w ++ [a]) = 0) :
    TrieState L lo (trieNew (T.set (nd (i, w) + a) T.length)) roots f
      (Function.update nd (i, w ++ [a]) T.length) := by
  have hin := h.inv.inside hw
  have hc : cells (trieNew (T.set (nd (i, w) + a) T.length)) =
      Function.update (cells T) (nd (i, w) + a) T.length := by
    rw [cells_trieNew, cells_set T _ _ (by omega)]
  refine ⟨by simpa only [hc, length_trieNew, List.length_set] using h.inv.newChild ha hw hz,
    fun j => by simp [h.root], fun x v hv => ?_⟩
  obtain ⟨hLen, hne, hval⟩ := h.value x v hv
  rw [Function.update_of_ne (by grind : x ≠ (i, w ++ [a])), hc]
  refine ⟨hLen, hne, Function.update_of_ne (fun he => ?_) .. |>.trans hval⟩
  obtain ⟨he, -⟩ := h.inv.cell_inj (b := 0) hne hw ha (by omega) he
  grind

/-- Descend from the current prefix, preserving the represented values at a new child and
updating the map only at the final leaf. -/
private theorem TrieState.insert (h : TrieState L lo T roots f nd) (v : ℤ) (key : List ℕ)
    (hw : nd (i, w) ≠ 0) (hL : w.length + key.length = L) (hkey : ∀ a ∈ key, a < 11) :
    InsertOK T (nd (i, w)) key ∧ ∃ nd',
      TrieState L lo (trieInsert T (nd (i, w)) key v) roots (Function.update f (i, w ++ key) (some v)) nd' := by
  induction key generalizing T nd w with
  | nil => simpa only [List.append_nil, trieInsert, InsertOK] using
      And.intro (h.inv.inside hw) ⟨nd, h.write (by simpa using hL) hw v⟩
  | cons a l ih =>
    obtain ⟨hp, hin⟩ := h.inv.inside hw
    have ha : a < 11 := hkey a (by simp)
    have hl : ∀ b ∈ l, b < 11 := fun b hb => hkey b (by simp [hb])
    rw [List.length_cons] at hL
    have hchild : T.getD (nd (i, w) + a) 0 = nd (i, w ++ [a]) := h.inv.child i w a (by omega) ha hw
    have hL' : (w ++ [a]).length + l.length = L := by grind
    rw [List.append_cons, trieInsert, InsertOK, hchild]
    by_cases hz : nd (i, w ++ [a]) = 0
    · obtain ⟨hok, hrep⟩ := ih (h.addChild ha hw (by omega) hz) (w := w ++ [a]) (by grind) hL' hl
      rw [Function.update_self] at hok hrep
      simpa [hz, hp, hin] using And.intro hok hrep
    · obtain ⟨hok, hrep⟩ := ih h (w := w ++ [a]) hz hL' hl
      simpa [hz, hp, hin, show 0 < nd (i, w ++ [a]) by omega] using And.intro hok hrep

/-! ## Lookup -/

/-- **Lookup.**  Following the symbols of a string whose vertex exists leads to that vertex, through
addresses inside the array. -/
private theorem trieWalk_spec (hinv : TrieInv L lo (cells T) nd T.length) (key : List ℕ)
    (hlen : w.length + key.length ≤ L) (hkey : ∀ d ∈ key, d < 11) (hne : nd (i, w ++ key) ≠ 0) :
    WalkOK T (nd (i, w)) key ∧ trieWalk T (nd (i, w)) key = nd (i, w ++ key) := by
  induction key generalizing w with
  | nil =>
    rw [List.append_nil] at hne ⊢
    exact ⟨hinv.inside hne, rfl⟩
  | cons d l ih =>
    rw [List.length_cons] at hlen
    rw [List.append_cons] at hne ⊢
    have hwd : nd (i, w ++ [d]) ≠ 0 := hinv.prefix_ne l hne
    have hw : nd (i, w) ≠ 0 := hinv.prefix_ne [d] hwd
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) :=
      hinv.child i w d (by omega) (hkey d (by simp)) hw
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    obtain ⟨hok, hwalk⟩ := ih (w := w ++ [d])
      (by rw [List.length_append, List.length_singleton]; omega)
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
def TrieRep (L lo : ℕ) (T : List ℤ) (roots : ℕ → ℕ) (f : ℕ × List ℕ → Option ℤ) : Prop :=
  ∃ nd, TrieState L lo T roots f nd

namespace TrieRep

/-- An array without tries: any array of positive length.  The tries will be built behind it: lo is
its length. -/
theorem empty (L : ℕ) (T : List ℤ) (hT : 0 < T.length) :
    TrieRep L T.length T (fun _ => 0) fun _ => none :=
  -- no prefix has a vertex, so the fields on vertices hold vacuously
  ⟨fun _ => 0, ⟨by constructor <;> grind [cells], fun _ => rfl, by simp⟩⟩

variable {L lo : ℕ} {T : List ℤ} {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}

/-- The array is not empty: the address 0 means that there is no vertex. -/
theorem length_pos (h : TrieRep L lo T roots f) : 0 < T.length := by
  obtain ⟨_, H⟩ := h
  exact Nat.lt_of_lt_of_le H.inv.lo_pos H.inv.fr_aligned.1

/-- Fewer stored values are a weaker claim. -/
theorem mono {g : ℕ × List ℕ → Option ℤ} (h : TrieRep L lo T roots f)
    (hg : ∀ x v, g x = some v → f x = some v) : TrieRep L lo T roots g := by
  obtain ⟨nd, H⟩ := h
  exact ⟨nd, H.inv, H.root, fun x v hx => H.value x v (hg _ _ hx)⟩

/-- A new, empty trie number i. -/
theorem new (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i = 0) :
    TrieRep L lo (trieNew T) (Function.update roots i T.length) f := by
  obtain ⟨nd, H⟩ := h
  refine ⟨Function.update nd (i, []) T.length, ?_, fun j => ?_, fun x v hx => ?_⟩
  · simpa only [cells_trieNew, length_trieNew] using H.inv.newRoot i (H.root i |>.trans hi)
  · by_cases hji : j = i <;> simp [hji, H.root]
  · obtain ⟨hL, hn, hv⟩ := H.value x v hx
    simpa only [Function.update_of_ne (by grind [H.root] : x ≠ (i, [])), cells_trieNew]
      using And.intro hL (And.intro hn hv)

/-- Insertion at the root, including the bounds on all addresses it reads. -/
private theorem insert_spec (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0)
    (key : List ℕ) (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
    InsertOK T (roots i) key ∧
      TrieRep L lo (trieInsert T (roots i) key v) roots (Function.update f (i, key) (some v)) := by
  obtain ⟨nd, H⟩ := h
  simpa only [TrieRep, H.root, List.nil_append] using
    H.insert (i := i) (w := []) v key (by rwa [H.root]) (by simpa using hk) hd

/-- Storing a value. -/
theorem insert (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
    TrieRep L lo (trieInsert T (roots i) key v) roots (Function.update f (i, key) (some v)) :=
  (h.insert_spec i hi key hk hd v).2

/-- During an insertion, every cell read holds 0 or the address of a vertex inside the array. -/
theorem insertOK (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) : InsertOK T (roots i) key :=
  (h.insert_spec i hi key hk hd 0).1

/-- What `trieWalk_spec` says about the way from the root of trie number i down a stored string. -/
private theorem walk_spec (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ)
    (hd : ∀ d ∈ key, d < 11) (v : ℤ) (hf : f (i, key) = some v) :
    WalkOK T (roots i) key ∧ T.getD (trieWalk T (roots i) key) 0 = v := by
  obtain ⟨nd, H⟩ := h
  obtain ⟨hlen, hne, hv⟩ := H.value (i, key) v hf
  obtain ⟨hok, hwalk⟩ := trieWalk_spec (i := i) (w := []) H.inv key (by simp [← hlen]) hd hne
  rw [H.root] at hok hwalk
  exact ⟨hok, by rw [hwalk]; exact hv⟩

/-- Looking up a stored value. -/
theorem lookup (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ) (hd : ∀ d ∈ key, d < 11) (v : ℤ)
    (hf : f (i, key) = some v) : trieLookup T (roots i) key = v :=
  (h.walk_spec i key hd v hf).2

/-- On the way down a stored string, every cell read holds the address of a vertex inside the
array. -/
theorem walkOK (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ) (hd : ∀ d ∈ key, d < 11) (v : ℤ)
    (hf : f (i, key) = some v) : WalkOK T (roots i) key :=
  (h.walk_spec i key hd v hf).1

end TrieRep

end

end ThreeSumApsp.Spec
