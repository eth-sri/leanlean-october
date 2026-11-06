module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Induction
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Spec.Sec4.Theorem30.QueryLists
public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout

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
  induction key generalizing T p with
  | nil => simp [trieInsert]
  | cons d l ih =>
    rw [trieInsert, List.length_cons]
    split_ifs
    · have := ih (trieNew (T.set (p + d) T.length)) T.length
      rw [length_trieNew, List.length_set] at this
      omega
    · have := ih T (T.getD (p + d) 0).toNat
      omega

/-! ## Arrays as functions -/

/-- The cells of an array, as a function; beyond the end of the array it is 0. -/
def cells (T : List ℤ) : ℕ → ℤ := fun a => T.getD a 0

theorem cells_set (T : List ℤ) (a : ℕ) (z : ℤ) (ha : a < T.length) :
    cells (T.set a z) = Function.update (cells T) a z := by
  funext x
  by_cases hx : x = a
  · subst hx
    simp [cells, ha]
  · rw [Function.update_of_ne hx]
    simp only [cells, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hx)]

theorem cells_trieNew (T : List ℤ) : cells (trieNew T) = cells T := by
  funext x
  simp only [cells, trieNew, List.getD_eq_getElem?_getD]
  by_cases hx : x < T.length
  · rw [List.getElem?_append_left hx]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega : T.length ≤ x),
      List.getElem?_replicate]
    split_ifs <;> rfl

theorem cells_of_le (T : List ℤ) (a : ℕ) (ha : T.length ≤ a) : cells T a = 0 := by
  simp [cells, List.getD_eq_getElem?_getD, List.getElem?_eq_none ha]

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
theorem inside (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} (hx : nd x ≠ 0) :
    0 < nd x ∧ nd x + 11 ≤ fr :=
  ⟨Nat.pos_of_ne_zero hx, (h.range x hx).2.1⟩

/-- The blocks of different vertices are disjoint. -/
theorem cell_inj (h : TrieInv L lo μ nd fr) {x y : ℕ × List ℕ} {a b : ℕ} (hx : nd x ≠ 0)
    (hy : nd y ≠ 0) (ha : a < 11) (hb : b < 11) (hcell : nd x + b = nd y + a) :
    x = y ∧ b = a := by
  have := h.range x hx
  have := h.range y hy
  -- both addresses are lo plus a multiple of 11, and a, b < 11
  exact ⟨h.inj x y hx (by omega), by omega⟩

/-- The prefixes of a prefix that has a vertex have vertices. -/
theorem prefix_ne (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (l : List ℕ)
    (hw : nd (i, w ++ l) ≠ 0) : nd (i, w) ≠ 0 := by
  induction l using List.reverseRecOn with
  | nil => simpa using hw
  | append_singleton l a ih =>
    rw [← List.append_assoc] at hw
    exact ih (h.closed _ _ _ hw)

/-- A new vertex x at the address fr; its parent, if x is not a root, is a vertex already.  The
cells may change, as long as those from fr on stay free and the cells of the old vertices point to
the children, x among them. -/
theorem addVertex (h : TrieInv L lo μ nd fr) {x : ℕ × List ℕ} {μ' : ℕ → ℤ} (hx : nd x = 0)
    (hparent : ∀ i w a, (i, w ++ [a]) = x → nd (i, w) ≠ 0) (hfresh : ∀ c, fr ≤ c → μ' c = 0)
    (hchild : ∀ i w a, w.length < L → a < 11 → nd (i, w) ≠ 0 →
      μ' (nd (i, w) + a) = Function.update nd x fr (i, w ++ [a])) :
    TrieInv L lo μ' (Function.update nd x fr) (fr + 11) := by
  have hlo := h.lo_pos
  have := h.fr_aligned
  refine { child := fun i w a hw ha hnd => ?_, range := fun y hnd => ?_,
           inj := fun y y' hnd heq => ?_, closed := fun i w a hnd => ?_,
           fresh := fun c hc => hfresh c (by omega), lo_pos := hlo,
           fr_aligned := ⟨by omega, by omega⟩ }
  · -- child
    by_cases hwx : (i, w) = x
    · -- the new vertex has no children
      have hne : (i, w ++ [a]) ≠ x := fun happ => by simp [← hwx] at happ
      have hnone : nd (i, w ++ [a]) = 0 := by
        by_contra hc
        exact h.closed _ _ _ hc (by rw [hwx, hx])
      rw [hwx, Function.update_self, Function.update_of_ne hne, hfresh _ (by omega), hnone]
      rfl
    · rw [Function.update_of_ne hwx] at hnd ⊢
      exact hchild i w a hw ha hnd
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
    · rw [hwx, Function.update_self]
      omega
    · rw [Function.update_of_ne hwx]
      by_cases happ : (i, w ++ [a]) = x
      · exact hparent i w a happ
      · exact h.closed i w a (by rwa [Function.update_of_ne happ] at hnd)

/-- A new trie number i: its root is a new vertex at the address fr. -/
theorem newRoot (h : TrieInv L lo μ nd fr) (i : ℕ) (hi : nd (i, []) = 0) :
    TrieInv L lo μ (Function.update nd (i, []) fr) (fr + 11) := by
  have hne : ∀ (j : ℕ) (w : List ℕ) (a : ℕ), (j, w ++ [a]) ≠ (i, []) := fun j w a happ => by
    simp at happ
  refine h.addVertex hi (fun j w a happ => absurd happ (hne j w a)) h.fresh
    fun j w a hw ha hnd => ?_
  rw [Function.update_of_ne (hne j w a), h.child j w a hw ha hnd]

/-- A new vertex for the prefix w ++ [a], at the address fr, with the pointer to it in the vertex
of w. -/
theorem newChild (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} {a : ℕ} (ha : a < 11)
    (hw : nd (i, w) ≠ 0) (hwa : nd (i, w ++ [a]) = 0) :
    TrieInv L lo (Function.update μ (nd (i, w) + a) fr) (Function.update nd (i, w ++ [a]) fr)
      (fr + 11) := by
  have := h.inside hw
  refine h.addVertex hwa (fun j u b happ => ?_) (fun c hc => ?_) fun j u b hu hb hnd => ?_
  · obtain ⟨rfl, happ'⟩ := Prod.mk.inj happ
    rwa [(List.append_inj' happ' rfl).1]
  · rw [Function.update_of_ne (by omega), h.fresh c hc]
  · by_cases hcell : nd (j, u) + b = nd (i, w) + a
    · obtain ⟨hju, rfl⟩ := h.cell_inj hnd hw ha hb hcell
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hju
      rw [Function.update_self, Function.update_self]
    · have hne : (j, u ++ [b]) ≠ (i, w ++ [a]) := fun happ => by
        obtain ⟨rfl, happ'⟩ := Prod.mk.inj happ
        obtain ⟨rfl, hba⟩ := List.append_inj' happ' rfl
        exact hcell (by rw [List.singleton_inj.mp hba])
      rw [Function.update_of_ne hcell, Function.update_of_ne hne, h.child j u b hu hb hnd]

/-- Writing a value into the vertex of a string of full length. -/
theorem setVal (h : TrieInv L lo μ nd fr) {i : ℕ} {w : List ℕ} (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (z : ℤ) : TrieInv L lo (Function.update μ (nd (i, w)) z) nd fr := by
  have := h.inside hw
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
structure TrieExt (L : ℕ) (x : ℕ × List ℕ) (μ : ℕ → ℤ) (nd : ℕ × List ℕ → ℕ) (μ' : ℕ → ℤ)
    (nd' : ℕ × List ℕ → ℕ) : Prop where
  old_vertex : ∀ y, nd y ≠ 0 → nd' y = nd y
  old_root : ∀ i, nd' (i, []) ≠ 0 → nd (i, []) ≠ 0
  old_value : ∀ i w, w.length = L → nd (i, w) ≠ 0 → (i, w) ≠ x → μ' (nd (i, w)) = μ (nd (i, w))

theorem TrieExt.trans {L : ℕ} {x : ℕ × List ℕ} {μ μ₁ μ₂ : ℕ → ℤ}
    {nd nd₁ nd₂ : ℕ × List ℕ → ℕ} (h : TrieExt L x μ nd μ₁ nd₁) (h' : TrieExt L x μ₁ nd₁ μ₂ nd₂) :
    TrieExt L x μ nd μ₂ nd₂ := by
  have hne : ∀ y, nd y ≠ 0 → nd₁ y ≠ 0 := fun y hy => by rwa [h.old_vertex y hy]
  refine { old_vertex := fun y hy => ?_, old_root := fun i hi => h.old_root i (h'.old_root i hi),
           old_value := fun i w hL hw hx => ?_ }
  · rw [h'.old_vertex y (hne y hy), h.old_vertex y hy]
  · rw [← h.old_value i w hL hw hx, ← h.old_vertex _ hw, h'.old_value i w hL (hne _ hw) hx]

/-- T' with the vertices nd' is T with the vertices nd after the value v was stored for the string
x: the invariant holds, x has a vertex, the vertex holds v, and the tries have been extended. -/
structure Inserted (L lo : ℕ) (x : ℕ × List ℕ) (v : ℤ) (T : List ℤ) (nd : ℕ × List ℕ → ℕ)
    (T' : List ℤ) (nd' : ℕ × List ℕ → ℕ) : Prop where
  inv : TrieInv L lo (cells T') nd' T'.length
  vertex : nd' x ≠ 0
  value : cells T' (nd' x) = v
  ext : TrieExt L x (cells T) nd (cells T') nd'

/-- An insertion after a step that extends the tries. -/
theorem Inserted.of_step {L lo : ℕ} {x : ℕ × List ℕ} {v : ℤ} {T T₁ T₂ : List ℤ}
    {nd nd₁ nd₂ : ℕ × List ℕ → ℕ} (h : Inserted L lo x v T₁ nd₁ T₂ nd₂)
    (hstep : TrieExt L x (cells T) nd (cells T₁) nd₁) : Inserted L lo x v T nd T₂ nd₂ :=
  { h with ext := hstep.trans h.ext }

section

variable {L lo i : ℕ} {T : List ℤ} {nd : ℕ × List ℕ → ℕ} {w : List ℕ}

/-- The end of an insertion: the value is written into the vertex of the string. -/
theorem TrieInv.inserted_set (h : TrieInv L lo (cells T) nd T.length) (hL : w.length = L)
    (hw : nd (i, w) ≠ 0) (v : ℤ) : Inserted L lo (i, w) v T nd (T.set (nd (i, w)) v) nd := by
  have := h.inside hw
  have hcells : cells (T.set (nd (i, w)) v) = Function.update (cells T) (nd (i, w)) v :=
    cells_set T _ _ (by omega)
  refine { inv := ?_, vertex := hw, value := ?_,
           ext := { old_vertex := fun _ _ => rfl, old_root := fun _ hi => hi,
                    old_value := fun j u _ hu hne => ?_ } }
  · rw [hcells, List.length_set]
    exact h.setVal hL hw v
  · rw [hcells, Function.update_self]
  · rw [hcells, Function.update_of_ne fun hnd => hne (h.inj _ _ hu hnd)]

/-- A step of an insertion where there is no child: a new vertex at the end of the array keeps the
invariant and extends the tries. -/
theorem TrieInv.step_newChild (h : TrieInv L lo (cells T) nd T.length) {d : ℕ}
    (hd : d < 11) (hw : nd (i, w) ≠ 0) (hlen : w.length < L) (hnone : nd (i, w ++ [d]) = 0)
    (x : ℕ × List ℕ) :
    TrieInv L lo (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length)
        (trieNew (T.set (nd (i, w) + d) T.length)).length ∧
      TrieExt L x (cells T) nd (cells (trieNew (T.set (nd (i, w) + d) T.length)))
        (Function.update nd (i, w ++ [d]) T.length) := by
  have := h.inside hw
  rw [cells_trieNew, cells_set T _ _ (by omega), length_trieNew, List.length_set]
  refine ⟨h.newChild hd hw hnone,
    { old_vertex := fun y hy => ?_, old_root := fun j hj => ?_,
      old_value := fun j u hL hu _ => ?_ }⟩
  · exact Function.update_of_ne (fun hyw => hy (by rw [hyw, hnone])) _ _
  · rwa [Function.update_of_ne (by simp)] at hj
  · refine Function.update_of_ne (fun hcell => ?_) _ _
    obtain ⟨hju, -⟩ := h.cell_inj (b := 0) hu hw hd (by omega) hcell
    obtain ⟨-, rfl⟩ := Prod.mk.inj hju
    -- a vertex at depth L is not above depth L
    omega

/-- **Insertion.**  Below the vertex of the prefix w, the insertion of the rest of a string meets
only addresses inside the array, and it achieves what `Inserted` says. -/
theorem trieInsert_spec (v : ℤ) (key : List ℕ) (hinv : TrieInv L lo (cells T) nd T.length)
    (hw : nd (i, w) ≠ 0) (hlen : w.length + key.length = L) (hkey : ∀ d ∈ key, d < 11) :
    InsertOK T (nd (i, w)) key ∧
      ∃ nd', Inserted L lo (i, w ++ key) v T nd (trieInsert T (nd (i, w)) key v) nd' := by
  induction key generalizing T nd w with
  | nil =>
    rw [List.append_nil]
    exact ⟨hinv.inside hw, nd, hinv.inserted_set hlen hw v⟩
  | cons d l ih =>
    obtain ⟨hpos, hin⟩ := hinv.inside hw
    have hd : d < 11 := hkey d (by simp)
    have hl : ∀ x ∈ l, x < 11 := fun x hx => hkey x (by simp [hx])
    rw [List.length_cons] at hlen
    have hchild : T.getD (nd (i, w) + d) 0 = nd (i, w ++ [d]) := hinv.child i w d (by omega) hd hw
    have : (w ++ [d]).length + l.length = L := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [List.append_cons, trieInsert, InsertOK, hchild]
    by_cases hz : nd (i, w ++ [d]) = 0
    · -- there is no child: a new vertex at the end of the array
      obtain ⟨hinv₁, hstep⟩ := hinv.step_newChild hd hw (by omega) hz (i, w ++ [d] ++ l)
      obtain ⟨hok, nd', hins⟩ :=
        ih hinv₁ (w := w ++ [d]) (by rw [Function.update_self]; omega) this hl
      rw [Function.update_self] at hok hins
      rw [hz, Int.natCast_zero, if_pos rfl, if_pos rfl]
      exact ⟨⟨hpos, hin, hok⟩, nd', hins.of_step hstep⟩
    · -- the child exists
      obtain ⟨hok, nd', hins⟩ := ih hinv (w := w ++ [d]) hz this hl
      have hz' : (nd (i, w ++ [d]) : ℤ) ≠ 0 := by exact_mod_cast hz
      rw [if_neg hz', if_neg hz', Int.toNat_natCast]
      exact ⟨⟨hpos, hin, by omega, hok⟩, nd', hins⟩

/-! ## Lookup -/

/-- **Lookup.**  Following the symbols of a string whose vertex exists leads to that vertex, through
addresses inside the array. -/
theorem trieWalk_spec (hinv : TrieInv L lo (cells T) nd T.length) (key : List ℕ)
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

/-! ## The interface -/

/-- The array T holds, from the address lo on, tries number 0, 1, … for strings of L symbols.  The
root of trie number i is at the address roots i (0 if the trie does not exist yet), and every entry
f (i, key) = some v is stored: the string key has the value v in trie number i.  The array may hold
more than f lists. -/
def TrieRep (L lo : ℕ) (T : List ℤ) (roots : ℕ → ℕ) (f : ℕ × List ℕ → Option ℤ) : Prop :=
  ∃ nd, TrieInv L lo (cells T) nd T.length ∧ (∀ i, nd (i, []) = roots i) ∧
    ∀ i key v, f (i, key) = some v → key.length = L ∧ nd (i, key) ≠ 0 ∧ cells T (nd (i, key)) = v

namespace TrieRep

/-- An array without tries: any array of positive length.  The tries will be built behind it: lo is
its length. -/
theorem empty (L : ℕ) (T : List ℤ) (hT : 0 < T.length) :
    TrieRep L T.length T (fun _ => 0) fun _ => none :=
  -- no prefix has a vertex, so the fields on vertices hold vacuously
  ⟨fun _ => 0,
    { child := fun _ _ _ _ _ h => absurd rfl h, range := fun _ h => absurd rfl h,
      inj := fun _ _ h => absurd rfl h, closed := fun _ _ _ h => absurd rfl h,
      fresh := fun a ha => cells_of_le T a ha, lo_pos := hT,
      fr_aligned := ⟨Nat.le_refl _, by simp⟩ },
    fun _ => rfl, fun _ _ _ h => by simp at h⟩

variable {L lo : ℕ} {T : List ℤ} {roots : ℕ → ℕ} {f : ℕ × List ℕ → Option ℤ}

/-- The array is not empty: the address 0 means that there is no vertex. -/
theorem length_pos (h : TrieRep L lo T roots f) : 0 < T.length := by
  obtain ⟨nd, hinv, -, -⟩ := h
  exact Nat.lt_of_lt_of_le hinv.lo_pos hinv.fr_aligned.1

/-- Fewer stored values are a weaker claim. -/
theorem mono {g : ℕ × List ℕ → Option ℤ} (h : TrieRep L lo T roots f)
    (hg : ∀ x v, g x = some v → f x = some v) : TrieRep L lo T roots g := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  exact ⟨nd, hinv, hroots, fun i key v hx => hval i key v (hg _ v hx)⟩

/-- A new, empty trie number i. -/
theorem new (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i = 0) :
    TrieRep L lo (trieNew T) (Function.update roots i T.length) f := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  refine ⟨Function.update nd (i, []) T.length, ?_, fun j => ?_, fun j key v hf => ?_⟩
  · rw [cells_trieNew, length_trieNew]
    exact hinv.newRoot i (by rw [hroots, hi])
  · by_cases hsame : j = i
    · rw [hsame, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hsame, Function.update_of_ne (by simpa using hsame), hroots]
  · obtain ⟨hlen, hne, hv⟩ := hval j key v hf
    rw [Function.update_of_ne fun hkey => hne (by rw [hkey, hroots, hi]), cells_trieNew]
    exact ⟨hlen, hne, hv⟩

/-- What `trieInsert_spec` says about an insertion from the root of trie number i. -/
theorem insert_spec (nd : ℕ × List ℕ → ℕ) (hinv : TrieInv L lo (cells T) nd T.length)
    (hroots : ∀ i, nd (i, []) = roots i) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
    InsertOK T (roots i) key ∧
      ∃ nd', Inserted L lo (i, key) v T nd (trieInsert T (roots i) key v) nd' := by
  have h := trieInsert_spec (i := i) (w := []) v key hinv (by rwa [hroots]) (by simpa using hk) hd
  rwa [hroots] at h

/-- Storing a value. -/
theorem insert (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) (v : ℤ) :
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

/-- During an insertion, every cell read holds 0 or the address of a vertex inside the array. -/
theorem insertOK (h : TrieRep L lo T roots f) (i : ℕ) (hi : roots i ≠ 0) (key : List ℕ)
    (hk : key.length = L) (hd : ∀ d ∈ key, d < 11) : InsertOK T (roots i) key := by
  obtain ⟨nd, hinv, hroots, -⟩ := h
  exact (insert_spec nd hinv hroots i hi key hk hd 0).1

/-- What `trieWalk_spec` says about the way from the root of trie number i down a stored string. -/
theorem walk_spec (h : TrieRep L lo T roots f) (i : ℕ) (key : List ℕ)
    (hd : ∀ d ∈ key, d < 11) (v : ℤ) (hf : f (i, key) = some v) :
    WalkOK T (roots i) key ∧ T.getD (trieWalk T (roots i) key) 0 = v := by
  obtain ⟨nd, hinv, hroots, hval⟩ := h
  obtain ⟨hlen, hne, hv⟩ := hval i key v hf
  obtain ⟨hok, hwalk⟩ := trieWalk_spec (i := i) (w := []) hinv key (by simp [hlen]) hd hne
  rw [hroots] at hok hwalk
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


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The boxes with e stars, as a list (proof of Lemma 29)

"A box in which f of the symbols are P₀ or stars is obtained from a leaf of order m - f (namely the
leaf we get by replacing its stars with P₀) by turning the e lowest symbols P₀ of that leaf into
stars, for some e ≤ f."  So the boxes with exactly e stars are the leaves with between e and m - t
symbols P₀, with the first e digits 9 turned into 10: this is `starBoxes`.

The list contains exactly the boxes with e stars (`mem_starBoxes`, `exists_of_mem_starBoxes`), each
of them once (`starBoxes_nodup`), so it has as many members as there are such boxes
(`length_starBoxes`), and all lists together have as many members as there are boxes
(`sum_length_starBoxes`).

The lists are the order of work of Lemma 29: "We compute the values of the boxes in increasing order
of their number of stars", "Generating the boxes with e stars and inserting them into the trie".
All of them go into the trie of the tile.  The number of stars can be read off a box
(`starCount_of_mem_starBoxes`), so boxes from different lists are different strings, and a string
is a box exactly if it is in the list for its number of stars (`isBoxDigits_digitsC`).  There are
boxes with e stars only for e ≤ m - t (`le_of_mem_starBoxes`).  Replacing the highest star of a box
with e + 1 stars by a term gives a box with e stars (`exists_lastStar_of_mem_starBoxes`).
-/



/-- The boxes with e stars, as lists of digits. -/
def starBoxes (L m t e : ℕ) : List (List ℕ) := (nineStrs L e (m - t)).map (starFirst e)

theorem length_starBoxes_eq_length_nineStrs (L m t e : ℕ) :
    (starBoxes L m t e).length = (nineStrs L e (m - t)).length :=
  List.length_map _

/-- Box number i comes from leaf number i. -/
theorem starFirst_mem_starBoxes {L m t e i : ℕ} (hi : i < (nineStrs L e (m - t)).length) :
    starFirst e (nineStrs L e (m - t))[i] ∈ starBoxes L m t e :=
  List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩

/-- A member of the list comes from a leaf with between e and m - t symbols P₀. -/
theorem exists_leaf_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t e) :
    ∃ τ : Leaf L, e ≤ (P0Levels τ).card ∧ (P0Levels τ).card ≤ m - t ∧
      digitsC (starLowest e τ) = l := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs l').1 hl'
  obtain ⟨τ, rfl⟩ := exists_digitsT (L := L) l' hlen hdig
  exact ⟨τ, by rwa [card_P0Levels], by rwa [card_P0Levels], digitsC_starLowest e τ⟩

/-- The list contains exactly the boxes with e stars. -/
theorem mem_starBoxes {L : ℕ} (m t e : ℕ) (π : Cube L) :
    digitsC π ∈ starBoxes L m t e ↔ π ∈ boxesWithStars L m t e := by
  rw [mem_boxesWithStars]
  constructor
  · intro h
    obtain ⟨τ, hlo, hhi, hτ⟩ := exists_leaf_of_mem_starBoxes h
    obtain rfl : π = starLowest e τ := digitsC_injective L hτ.symm
    refine ⟨isBox_starLowest m t e τ hhi, ?_⟩
    rw [starLevels_starLowest, card_lowest]
    omega
  · rintro ⟨hbox, he⟩
    have hπ := eq_starLowest_starsToP0 π hbox.2
    have hcard := card_P0Levels_starsToP0 π
    rw [he] at hπ
    refine List.mem_map.2 ⟨digitsT (Cube.starsToP0 π),
      (mem_nineStrs _).2 ⟨length_digitsT _, digitsT_lt _, ?_, ?_⟩, ?_⟩
    · rw [← card_P0Levels]
      omega
    · rw [← card_P0Levels, hcard]
      exact hbox.1
    · rw [← digitsC_starLowest, ← hπ]

/-- Every member of the list is a cube. -/
theorem exists_of_mem_starBoxes {L m t e : ℕ} (l : List ℕ) (h : l ∈ starBoxes L m t e) :
    ∃ π : Cube L, digitsC π = l := by
  obtain ⟨τ, -, -, hτ⟩ := exists_leaf_of_mem_starBoxes h
  exact ⟨_, hτ⟩

/-- The number of stars can be read off a member of the list: the star is a symbol of its own, the
digit 10.  So boxes with different numbers of stars are different strings. -/
theorem starCount_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    starCount l = e := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  rw [← card_starLevels]
  exact (mem_boxesWithStars.1 ((mem_starBoxes m t e π).1 h)).2

/-- The string l is a box: it is in the list of the boxes with its number of stars. -/
abbrev IsBoxDigits (L m t : ℕ) (l : List ℕ) : Prop := l ∈ starBoxes L m t (starCount l)

theorem isBoxDigits_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    IsBoxDigits L m t l := by
  rwa [IsBoxDigits, starCount_of_mem_starBoxes h]

/-- A string of symbols is in the list of the boxes with its number of stars exactly if it is a
box. -/
theorem isBoxDigits_digitsC {L : ℕ} (m t : ℕ) (π : Cube L) :
    IsBoxDigits L m t (digitsC π) ↔ π ∈ boxes L m t := by
  rw [IsBoxDigits, ← card_starLevels, mem_starBoxes, mem_boxesWithStars, mem_boxes]
  exact and_iff_left rfl

/-- There are boxes with e stars only for e ≤ m - t. -/
theorem le_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) : e ≤ m - t := by
  obtain ⟨τ, hlo, hhi, -⟩ := exists_leaf_of_mem_starBoxes h
  exact hlo.trans hhi

/-- The members of the lists are strings of L digits below 11. -/
theorem starBoxes_digits {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    l.length = L ∧ ∀ d ∈ l, d < 11 := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  exact ⟨length_digitsC π, digitsC_lt π⟩

/-- Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars (proof
of Lemma 29). -/
theorem exists_lastStar_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t (e + 1)) :
    ∃ p, lastStar l = some p ∧ ∀ d < 10, l.set p d ∈ starBoxes L m t e := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  have hπ : π ∈ boxesWithStars L m t (e + 1) := (mem_starBoxes m t (e + 1) π).mp h
  have : (Cube.starLevels π).card = e + 1 := (Finset.mem_filter.mp hπ).2
  have hne : (Cube.starLevels π).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨_, lastStar_digitsC π hne, fun d hd => ?_⟩
  have hsplit := lemma_29_split hπ hne (termEquiv.symm ⟨d, hd⟩)
  rw [← mem_starBoxes, digitsC_replace] at hsplit
  have hidx : ((termIdx (termEquiv.symm ⟨d, hd⟩) : Fin 10) : ℕ) = d :=
    congrArg Fin.val (termEquiv.apply_symm_apply ⟨d, hd⟩)
  rwa [hidx] at hsplit

/-- No box occurs twice in the list: turning the stars back into nines gives the leaf. -/
theorem starBoxes_nodup (L m t e : ℕ) : (starBoxes L m t e).Nodup := by
  refine (nineStrs_nodup _ _ _).map_on fun x hx y hy h => ?_
  rw [← starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hx), h,
    starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hy)]

/-- The list has as many members as there are boxes with e stars. -/
theorem length_starBoxes (L m t e : ℕ) :
    (starBoxes L m t e).length = (boxesWithStars L m t e).card := by
  classical
  have himage : (boxesWithStars L m t e).image digitsC = (starBoxes L m t e).toFinset := by
    ext l
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact (mem_starBoxes m t e π).2 hπ
    · intro hl
      obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l hl
      exact ⟨π, (mem_starBoxes m t e π).1 hl, rfl⟩
  rw [← List.toFinset_card_of_nodup (starBoxes_nodup L m t e), ← himage,
    Finset.card_image_of_injective _ (digitsC_injective L)]

/-- All lists together have as many members as there are boxes (Lemma 29). -/
theorem sum_length_starBoxes (L m t : ℕ) :
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length).sum
      = (boxes L m t).card := by
  have hfibres : (boxes L m t).card = ∑ e ∈ Finset.range (m - t + 1),
      ((boxes L m t).filter fun π => (Cube.starLevels π).card = e).card := by
    refine Finset.card_eq_sum_card_fiberwise fun π hπ => ?_
    have := (mem_boxes.1 (Finset.mem_coe.1 hπ)).1
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [List.sum_map_range, hfibres]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [length_starBoxes]
  refine congrArg Finset.card (Finset.ext fun π => ?_)
  rw [mem_boxesWithStars, Finset.mem_filter, mem_boxes]


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The trie of a tile, and the tries of all tiles (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  `tileTrie` builds this trie.

"We compute the values of the boxes in increasing order of their number of stars": `fillUpTo` goes
through the boxes with 0, 1, … stars (`starBoxes`), and `fillTrie` inserts the boxes with e stars
with their values (`boxValue`): the value of a box without stars is "the product of its two numbers
in the encodings", the value of a box with stars is computed "with ten lookups in the trie" of the
tile.  `allTries` does this for all tiles, in one array; the number of a trie is the number of its
tile.  The array and the list of the roots form a record `TrieStore`.

What the array holds at a moment is a function from pairs (the number of a trie, a box) to values:
`storedUpTo` in the middle of a tile, `storedAll` between two tiles.
1. One more box is one more entry, the state after all boxes with k stars is the state before the
   first box with k + 1 stars, and a complete tile adds its boxes to `storedAll`
   (`storedUpTo_snoc`, `storedUpTo_succ`, `storedAll_snoc`).
2. Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars
   (`exists_lastStar_of_mem_starBoxes`); so, once the boxes with e stars are stored, the value
   computed for the box is that of the dynamic program (`boxValue_eq`).
3. So the array represents these functions, in the sense of `TrieRep`, after some boxes with e stars
   (`fillTrie_rep`), after all boxes with fewer than k stars (`fillUpTo_rep`) and after some tiles
   (`allTries_rep`).
4. Hence a lookup returns the value of the dynamic program of Lemma 29 (`lookup_allTries`), which is
   the value of the box: the array holds "for every tile, the values of all its boxes"
   (`lookup_allTries_eq_val`).  Every box that a query reads is there (`boxesOf_mem_starBoxes`).
5. Space: "O(L) […] space per box" (`length_tileTrie_le`, `length_allTries_le`).
6. The bottom line, for any list of tiles: the query that reads the values of its boxes from the
   trie of its tile (`trieQuery`) returns `queryValue` (`trieQuery_allTries`), and all its walks
   down the trie are safe (`walkOK_allTries`).  The tiles of the product are `tileList`, and
   `tilesBefore` is its part before a tile.

Two ladders lead from the arrays to the paper.
* A query: `trieQuery` adds up `queryTerms` with the values read from the trie; these are the values
  of the dynamic program (`queryTerms_allTries`), with which the sum is `queryValue` on cubes
  (`sum_queryTerms_storedD`), which is `querySum`, the sum of Lemma 28 (`lemma_29_values`, inside
  `Theorem30.correct`), which is the entry `(X * Y) I J` (`Theorem30.query`).
* The value of a box: `boxValue` reads from the trie; it is `dpValueD` on lists of digits
  (`boxValue_eq`), which is `dpValue` on cubes (`dpValueD_digitsC`), which is `Cube.val`
  (`lemma_29_values`).  `lookup_allTries_eq_val` is the whole ladder; no other proof rests on it.
-/



/-! ## Building the tries -/

/-- A tile, given by the arrays of its two encodings. -/
structure TileEnc where
  encA : List ℤ
  encB : List ℤ

/-- The tries of some tiles in one array: the array, and the addresses of the roots.  The trie of
tile number i has the root number i. -/
structure TrieStore where
  cells : List ℤ
  roots : List ℕ

namespace TrieStore

/-- The address of the root of trie number i, or 0 if there is no such trie. -/
def root (s : TrieStore) (i : ℕ) : ℕ := s.roots.getD i 0

/-- The value stored for the string l in trie number i. -/
def lookup (s : TrieStore) (i : ℕ) (l : List ℕ) : ℤ := trieLookup s.cells (s.root i) l

/-- The tries hold the entries of f, in the sense of `TrieRep`. -/
def Holds (L lo : ℕ) (s : TrieStore) (f : ℕ × List ℕ → Option ℤ) : Prop :=
  TrieRep L lo s.cells s.root f

/-- A new, empty trie behind the others. -/
def new (s : TrieStore) : TrieStore := ⟨trieNew s.cells, s.roots ++ [s.cells.length]⟩

/-- The new trie has the next number, and its root is at the old end of the array. -/
theorem root_new (s : TrieStore) : s.new.root s.roots.length = s.cells.length := by
  simp [root, new]

/-- A new, empty trie changes no entry. -/
theorem Holds.new {L lo : ℕ} {s : TrieStore} {f : ℕ × List ℕ → Option ℤ} (h : s.Holds L lo f) :
    s.new.Holds L lo f := by
  have hroot : s.new.root = Function.update s.root s.roots.length s.cells.length :=
    List.getD_append_singleton _ _ _
  rw [Holds, hroot]
  exact TrieRep.new h _ (List.getD_eq_default _ _ le_rfl)

end TrieStore

/-- The value of a box l (the paper's π) with e stars, computed from the array T: for e = 0 "the
product of its two numbers in the encodings"; for e ≥ 1 the sum val(π) = ∑_λ val(π[ℓ ← λ]), where ℓ
is "the highest level at which π has a star", computed "with ten lookups in the trie" of the tile,
which has the given root.  The function looks only at whether e = 0. -/
def boxValue (encA encB T : List ℤ) (root : ℕ) : ℕ → List ℕ → ℤ
  | 0, l => leafProduct encA encB (starsToNines l)
  | _ + 1, l => sumAtLastStar (trieLookup T root) l

/-- The value of a box without stars is the product at the leaf with its digits. -/
theorem boxValue_zero (encA encB T : List ℤ) (root : ℕ) {l : List ℕ} (hl : ∀ d ∈ l, d < 10) :
    boxValue encA encB T root 0 l = leafProduct encA encB l := by
  rw [boxValue, starsToNines_of_notMem fun h => absurd (hl 10 h) (lt_irrefl 10)]

/-- "Generating the boxes with e stars and inserting them into the trie": the array after some boxes
with e stars have been inserted into the trie of the tile, which has the given root, each with its
value, computed from the array as it is before the box is inserted. -/
def fillTrie (encA encB : List ℤ) (root e : ℕ) (boxes : List (List ℕ)) (T : List ℤ) : List ℤ :=
  boxes.foldl (fun T l => trieInsert T root l (boxValue encA encB T root e l)) T

/-- "We compute the values of the boxes in increasing order of their number of stars": the array
after the boxes with 0, …, k - 1 stars have been inserted, in this order, into the trie with the
given root. -/
def fillUpTo (encA encB : List ℤ) (L m t root : ℕ) : ℕ → List ℤ → List ℤ
  | 0, T => T
  | k + 1, T => fillTrie encA encB root k (starBoxes L m t k) (fillUpTo encA encB L m t root k T)

/-- The tries s with a new trie that holds the boxes with fewer than k stars. -/
def tileTrieUpTo (encA encB : List ℤ) (L m t : ℕ) (s : TrieStore) (k : ℕ) : TrieStore :=
  { s.new with cells := fillUpTo encA encB L m t s.cells.length k s.new.cells }

/-- Lemma 29: "Given the two encodings of a tile, we can compute the values of all these boxes, and
store them in the trie for that tile".  The trie is added to an array that may hold the tries of
other tiles already: a new root, and then all the boxes, which have at most m - t stars. -/
def tileTrie (encA encB : List ℤ) (L m t : ℕ) (s : TrieStore) : TrieStore :=
  tileTrieUpTo encA encB L m t s (m - t + 1)

/-- The tries of all tiles in one array: the trie of tile number i has the number i.  Cell 0 is left
unused, since the address 0 means: no vertex. -/
def allTries (L m t : ℕ) (tiles : List TileEnc) : TrieStore :=
  tiles.foldl (fun s ab => tileTrie ab.encA ab.encB L m t s) ⟨[0], []⟩

/-- The query of Theorem 30.  For every box of the output string "we look up its value in the trie
of the tile", which has the given root. -/
def trieQuery (m t : ℕ) (encA encB T : List ℤ) (root : ℕ) (w : List ℕ) : ℤ :=
  (queryTerms m t encA encB (trieLookup T root) w).sum

theorem fillTrie_cons (encA encB : List ℤ) (root e : ℕ) (l : List ℕ)
    (boxes : List (List ℕ)) (T : List ℤ) :
    fillTrie encA encB root e (l :: boxes) T
      = fillTrie encA encB root e boxes (trieInsert T root l (boxValue encA encB T root e l)) := rfl

/-- The trie of one more tile is built on top of the tries of the tiles before it. -/
theorem allTries_snoc (L m t : ℕ) (tiles : List TileEnc) (ab : TileEnc) :
    allTries L m t (tiles ++ [ab]) = tileTrie ab.encA ab.encB L m t (allTries L m t tiles) := by
  simp [allTries, List.foldl_append]

/-- Every box that a query reads is a box of the tile. -/
theorem boxesOf_mem_starBoxes {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) (l : List ℕ) (hl : l ∈ boxesOf m t (digitsO η)) :
    IsBoxDigits L m t l := by
  obtain ⟨π, hπ, rfl⟩ := exists_of_mem_boxesOf ht hη l hl
  obtain ⟨V, hV, hπ⟩ := Finset.mem_biUnion.mp hπ
  exact (isBoxDigits_digitsC m t π).mpr (Theorem30.lookup hV hπ)

/-! ## What the tries hold -/

/-- What the tries hold in the middle of tile number i: on top of the entries old, trie number i
holds the boxes with fewer than k stars and the boxes in pre (some boxes with k stars).  The entry
for the key (i, l) is the value `storedD encA encB l` of the dynamic program. -/
def storedUpTo (old : ℕ × List ℕ → Option ℤ) (i : ℕ) (encA encB : List ℤ) (L m t k : ℕ)
    (pre : List (List ℕ)) : ℕ × List ℕ → Option ℤ
  | (n, l) =>
    if n = i ∧ ((starCount l < k ∧ IsBoxDigits L m t l) ∨ l ∈ pre) then
      some (storedD encA encB l)
    else old (n, l)

/-- What the tries of all tiles hold, the third component of the data structure: "for every tile,
the values of all its boxes (the boxes are the same strings in every tile, but their values depend
on the input arrays of the tile)".  Trie number i holds the values of all boxes for tile number i.
The array holds at least these entries (`allTries_rep`, in the sense of `TrieRep`). -/
def storedAll (L m t : ℕ) (tiles : List TileEnc) : ℕ × List ℕ → Option ℤ
  | (n, l) =>
    if IsBoxDigits L m t l then tiles[n]?.map fun ab => storedD ab.encA ab.encB l else none

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L m t : ℕ}

/-- The boxes with fewer than k stars are stored with the values of the dynamic program. -/
theorem storedUpTo_of_lt {k e : ℕ} (pre : List (List ℕ)) {l : List ℕ} (he : e < k)
    (hl : l ∈ starBoxes L m t e) :
    storedUpTo old i encA encB L m t k pre (i, l) = some (dpValueD encA encB e l) := by
  obtain rfl := starCount_of_mem_starBoxes hl
  simp [storedUpTo, storedD, he, hl]

/-- Before the first box, there are the old entries only. -/
theorem storedUpTo_zero (x : ℕ × List ℕ) (v : ℤ)
    (h : storedUpTo old i encA encB L m t 0 [] x = some v) : old x = some v := by
  simpa [storedUpTo] using h

/-- One more box is one more entry. -/
theorem storedUpTo_snoc {e : ℕ} (pre : List (List ℕ)) {l : List ℕ}
    (hl : l ∈ starBoxes L m t e) :
    storedUpTo old i encA encB L m t e (pre ++ [l]) =
      Function.update (storedUpTo old i encA encB L m t e pre) (i, l)
        (some (dpValueD encA encB e l)) := by
  funext ⟨n, l'⟩
  by_cases hx : (n, l') = (i, l)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    simp [storedUpTo, storedD, starCount_of_mem_starBoxes hl]
  · rw [Function.update_of_ne hx]
    have : ¬ (n = i ∧ l' = l) := fun ⟨hn, hl'⟩ => hx (by rw [hn, hl'])
    simp only [storedUpTo, List.mem_append, List.mem_singleton]
    -- the two conditions differ only at the key (i, l)
    exact if_congr (by tauto) rfl rfl

/-- The state after all boxes with k stars is the state before the first box with k + 1 stars. -/
theorem storedUpTo_succ (k : ℕ) :
    storedUpTo old i encA encB L m t (k + 1) [] =
      storedUpTo old i encA encB L m t k (starBoxes L m t k) := by
  funext ⟨n, l⟩
  simp only [storedUpTo, List.not_mem_nil, or_false]
  refine if_congr (and_congr_right fun _ => ?_) rfl rfl
  rw [Nat.lt_succ_iff_lt_or_eq, or_and_right]
  exact or_congr_right
    ⟨fun h => h.1 ▸ h.2, fun h => ⟨starCount_of_mem_starBoxes h, isBoxDigits_of_mem_starBoxes h⟩⟩

end

/-- The boxes of tile number i are stored with the values of its dynamic program. -/
theorem storedAll_of_mem {L m t : ℕ} {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
    {l : List ℕ} (hi : tiles[i]? = some ab) (hl : IsBoxDigits L m t l) :
    storedAll L m t tiles (i, l) = some (storedD ab.encA ab.encB l) := by
  simp [storedAll, hl, hi]

/-- One more tile: what is stored then was stored before or belongs to the new tile. -/
theorem storedAll_snoc {L m t : ℕ} (tiles : List TileEnc) (ab : TileEnc)
    (x : ℕ × List ℕ) (v : ℤ) (h : storedAll L m t (tiles ++ [ab]) x = some v) :
    storedUpTo (storedAll L m t tiles) tiles.length ab.encA ab.encB L m t (m - t + 1) [] x
      = some v := by
  obtain ⟨n, l⟩ := x
  simp only [storedAll] at h
  split_ifs at h with hl
  simp only [storedUpTo]
  rcases Nat.lt_trichotomy n tiles.length with hn | hn | hn
  · -- an older tile
    rw [if_neg (by omega), ← h, List.getElem?_append_left hn]
    exact if_pos hl
  · -- the new tile
    rw [if_pos ⟨hn, Or.inl ⟨Nat.lt_succ_of_le (le_of_mem_starBoxes hl), hl⟩⟩, ← h, hn]
    simp
  · -- there is no such tile
    rw [List.getElem?_eq_none (by simp; omega)] at h
    simp at h

/-! ## The array represents what it should hold -/

section

variable {old : ℕ × List ℕ → Option ℤ} {i : ℕ} {encA encB : List ℤ} {L lo m t e : ℕ}
  {roots : ℕ → ℕ}

/-- With the boxes with fewer stars stored, the value computed for a box is the value of the dynamic
program. -/
theorem boxValue_eq {T : List ℤ} {pre : List (List ℕ)} {l : List ℕ}
    (h : TrieRep L lo T roots (storedUpTo old i encA encB L m t e pre))
    (hl : l ∈ starBoxes L m t e) : boxValue encA encB T (roots i) e l = dpValueD encA encB e l := by
  cases e with
  | zero => rfl
  | succ e =>
    obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hl
    exact sumAtLastStar_congr hp fun d hd => h.lookup i _ (starBoxes_digits (hset d hd)).2 _
      (storedUpTo_of_lt pre (Nat.lt_succ_self e) (hset d hd))

/-- Inserting boxes with e stars into the trie of the tile: if the array represents the state after
the boxes of pre, then after inserting the boxes of rest it represents the state after
pre ++ rest. -/
theorem fillTrie_rep (hi : roots i ≠ 0) (rest pre : List (List ℕ)) (T : List ℤ)
    (hmem : ∀ l ∈ rest, l ∈ starBoxes L m t e)
    (hrep : TrieRep L lo T roots (storedUpTo old i encA encB L m t e pre)) :
    TrieRep L lo (fillTrie encA encB (roots i) e rest T) roots
      (storedUpTo old i encA encB L m t e (pre ++ rest)) := by
  induction rest generalizing pre T with
  | nil => rwa [List.append_nil]
  | cons l rest ih =>
    have hl : l ∈ starBoxes L m t e := hmem l (by simp)
    have hins := hrep.insert i hi l (starBoxes_digits hl).1 (starBoxes_digits hl).2
      (boxValue encA encB T (roots i) e l)
    rw [boxValue_eq hrep hl, ← storedUpTo_snoc pre hl] at hins
    rw [fillTrie_cons, List.append_cons, boxValue_eq hrep hl]
    exact ih (pre ++ [l]) _ (fun x hx => hmem x (by simp [hx])) hins

end

/-- After k rounds the trie of the tile holds the values of the dynamic program for the boxes with
fewer than k stars, and the older entries are kept. -/
theorem fillUpTo_rep {old : ℕ × List ℕ → Option ℤ} (encA encB : List ℤ) {L lo : ℕ} (m t : ℕ)
    (s : TrieStore) (hs : s.Holds L lo old) (k : ℕ) :
    (tileTrieUpTo encA encB L m t s k).Holds L lo
      (storedUpTo old s.roots.length encA encB L m t k []) := by
  induction k with
  | zero => exact hs.new.mono storedUpTo_zero
  | succ k ih =>
    have hfill := fillTrie_rep (roots := s.new.root) (by rw [s.root_new]; exact hs.length_pos.ne')
      (starBoxes L m t k) [] _ (fun _ hl => hl) ih
    rw [storedUpTo_succ]
    rwa [s.root_new] at hfill

section

variable (L m t : ℕ)

/-- There is one root for each tile. -/
theorem length_roots_allTries (tiles : List TileEnc) :
    (allTries L m t tiles).roots.length = tiles.length := by
  induction tiles using List.reverseRecOn with
  | nil => rfl
  | append_singleton tiles ab ih =>
    rw [allTries_snoc, List.length_append, List.length_singleton, ← ih]
    exact List.length_append

/-- The tries of all tiles hold the values of the dynamic programs of the tiles. -/
theorem allTries_rep (tiles : List TileEnc) :
    (allTries L m t tiles).Holds L 1 (storedAll L m t tiles) := by
  induction tiles using List.reverseRecOn with
  | nil => exact (TrieRep.empty L [0] (by simp)).mono fun x v hx => by simp [storedAll] at hx
  | append_singleton tiles ab ih =>
    have h := fillUpTo_rep ab.encA ab.encB m t _ ih (m - t + 1)
    rw [length_roots_allTries] at h
    rw [allTries_snoc]
    exact h.mono (storedAll_snoc tiles ab)

variable {L m t} {tiles : List TileEnc} {i : ℕ}

/-- Looking up a box of tile number i. -/
theorem lookup_allTries {ab : TileEnc} (hi : tiles[i]? = some ab) {l : List ℕ}
    (hl : IsBoxDigits L m t l) : (allTries L m t tiles).lookup i l = storedD ab.encA ab.encB l :=
  (allTries_rep L m t tiles).lookup i l (starBoxes_digits hl).2 _ (storedAll_of_mem hi hl)

end

/-! ## Space -/

section

variable (encA encB : List ℤ)

/-- Inserting boxes "adds at most L vertices per box". -/
theorem length_fillTrie_le (root e L : ℕ) (boxes : List (List ℕ))
    (hb : ∀ l ∈ boxes, l.length = L) (T : List ℤ) :
    (fillTrie encA encB root e boxes T).length ≤ T.length + 11 * L * boxes.length := by
  induction boxes generalizing T with
  | nil => exact le_rfl
  | cons l boxes ih =>
    have := ih (fun x hx => hb x (by simp [hx]))
      (trieInsert T root l (boxValue encA encB T root e l))
    have hins := length_trieInsert_le T root l (boxValue encA encB T root e l)
    rw [hb l (by simp)] at hins
    rw [fillTrie_cons, List.length_cons, Nat.mul_add_one]
    omega

variable (L m t : ℕ)

/-- The boxes with fewer than k stars take at most 11 L n cells, where n is their number. -/
theorem length_fillUpTo_le_sum (root k : ℕ) (T : List ℤ) :
    (fillUpTo encA encB L m t root k T).length
      ≤ T.length + 11 * L * ((List.range k).map fun e => (starBoxes L m t e).length).sum := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [fillUpTo, List.sum_range_succ, Nat.mul_add (11 * L)]
    have := length_fillTrie_le encA encB root k L (starBoxes L m t k)
      (fun l hl => (starBoxes_digits hl).1) (fillUpTo encA encB L m t root k T)
    omega

/-- Lemma 29, space: "O(L) […] space per box"; eleven cells more for the root. -/
theorem length_tileTrie_le (s : TrieStore) :
    (tileTrie encA encB L m t s).cells.length
      ≤ s.cells.length + 11 * (1 + L * (boxes L m t).card) := by
  have h := length_fillUpTo_le_sum encA encB L m t s.cells.length (m - t + 1) (trieNew s.cells)
  rw [sum_length_starBoxes, Nat.mul_assoc, length_trieNew] at h
  exact h.trans (by omega)

/-- All tiles together: cell 0, and for each tile the space of Lemma 29. -/
theorem length_allTries_le (tiles : List TileEnc) :
    (allTries L m t tiles).cells.length
      ≤ 1 + tiles.length * (11 * (1 + L * (boxes L m t).card)) := by
  induction tiles using List.reverseRecOn with
  | nil => simp [allTries]
  | append_singleton tiles ab ih =>
    rw [allTries_snoc]
    refine (length_tileTrie_le _ _ L m t _).trans ?_
    rw [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

end

/-! ## The list of all tiles -/

section

variable {L : ℕ} (nB : ℕ) (encA encB : ℕ → Leaf L → ℤ)

/-- The tiles in row-major order, each given by the arrays of its two encodings: tile (β, β') has
the number β nB + β'. -/
def tileList : List TileEnc :=
  (List.range nB).flatMap fun β => (List.range nB).map fun β' => ⟨arrT (encA β), arrT (encB β')⟩

/-- There are nB² tiles. -/
theorem length_tileList : (tileList nB encA encB).length = nB * nB :=
  List.length_flatMap_range nB _ fun _ _ => by simp

/-- Tile (β, β') has the number β nB + β'. -/
theorem getElem?_tileList {β β' : ℕ} (hβ : β < nB) (hβ' : β' < nB) :
    (tileList nB encA encB)[β * nB + β']? = some ⟨arrT (encA β), arrT (encB β')⟩ := by
  have hlt : β * nB + β' < (tileList nB encA encB).length :=
    (Nat.mul_add_lt_mul hβ hβ').trans_eq (length_tileList nB encA encB).symm
  rw [List.getElem?_eq_getElem hlt, ← List.getD_eq_getElem _ ⟨[], []⟩ hlt, tileList,
    List.getD_flatMap_range _ (fun _ _ => by simp) hβ hβ', List.getD_map_range _ hβ']

/-- The tiles before the tile (β, β'), in row-major order. -/
def tilesBefore (β β' : ℕ) : List TileEnc :=
  ((List.range β).flatMap fun b => (List.range nB).map fun b' => ⟨arrT (encA b), arrT (encB b')⟩) ++
    (List.range β').map fun b' => ⟨arrT (encA β), arrT (encB b')⟩

/-- No tile stands before the first one. -/
theorem tilesBefore_zero : tilesBefore nB encA encB 0 0 = [] := by
  simp [tilesBefore]

/-- The tiles before the next tile of the row are the tiles before the tile, and the tile. -/
theorem tilesBefore_succ (β β' : ℕ) :
    tilesBefore nB encA encB β (β' + 1)
      = tilesBefore nB encA encB β β' ++ [⟨arrT (encA β), arrT (encB β')⟩] := by
  simp [tilesBefore, List.range_succ]

/-- The end of a row is the beginning of the next one. -/
theorem tilesBefore_row (β : ℕ) :
    tilesBefore nB encA encB β nB = tilesBefore nB encA encB (β + 1) 0 := by
  simp [tilesBefore, List.range_succ, List.flatMap_append]

/-- After the last row all tiles have been taken. -/
theorem tilesBefore_all : tilesBefore nB encA encB nB 0 = tileList nB encA encB := by
  simp [tilesBefore, tileList]

/-- β nB + β' tiles stand before the tile (β, β'). -/
theorem length_tilesBefore (β β' : ℕ) :
    (tilesBefore nB encA encB β β').length = β * nB + β' := by
  simp [tilesBefore, List.length_flatMap]

end

/-! ## What the tries of all tiles give to a query

The query for tile number i gets the root of the trie of this tile. -/

section Query

variable {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ} {ab : TileEnc}
  (hi : tiles[i]? = some ab) {η : OutStr L} (hη : (innerSetO η).card = m)

include ht hi hη

/-- Every box of the query is stored: the walk down the trie is safe. -/
theorem walkOK_allTries {l : List ℕ} (hl : l ∈ boxesOf m t (digitsO η)) :
    WalkOK (allTries L m t tiles).cells ((allTries L m t tiles).root i) l := by
  have hbox := boxesOf_mem_starBoxes m t ht η hη l hl
  exact (allTries_rep L m t tiles).walkOK i l (starBoxes_digits hbox).2 _ (storedAll_of_mem hi hbox)

/-- The numbers that the query adds up, read from the trie, are those of the dynamic program. -/
theorem queryTerms_allTries :
    queryTerms m t ab.encA ab.encB ((allTries L m t tiles).lookup i) (digitsO η)
      = queryTerms m t ab.encA ab.encB (storedD ab.encA ab.encB) (digitsO η) :=
  congrArg _ (List.map_congr_left fun l hl =>
    lookup_allTries hi (boxesOf_mem_starBoxes m t ht η hη l hl))

end Query

/-- **The query on the tries of all tiles** returns the value of the query of the proof of
Theorem 30, which is the entry of the product (`Theorem30.correct`). -/
theorem trieQuery_allTries {L m t : ℕ} (ht : t ≤ m) {tiles : List TileEnc} {i : ℕ}
    (encA encB : Leaf L → ℤ) (hi : tiles[i]? = some ⟨arrT encA, arrT encB⟩) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    trieQuery m t (arrT encA) (arrT encB) (allTries L m t tiles).cells
        ((allTries L m t tiles).root i) (digitsO η)
      = queryValue m t encA encB η :=
  (congrArg List.sum (queryTerms_allTries ht hi hη)).trans
    (sum_queryTerms_storedD ht encA encB hη)

end ThreeSumApsp.Spec

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## Vocabulary -/

/-- The trie area of cap cells from tr: its first cells hold the array T, and the cell fp holds the
length of T. Nothing is assumed about the rest of the area. -/
structure TrieMem (μ : ℕ → ℤ) (tr cap fp : ℕ) (T : List ℤ) : Prop where
  seg : Seg μ tr T
  free : μ fp = T.length
  le_cap : T.length ≤ cap
  fp_out : fp < tr ∨ tr + cap ≤ fp

/-- The trie area stays as it is if its cells and the cell fp do not change. -/
theorem TrieMem.keep {μ μ' : ℕ → ℤ} {tr cap fp : ℕ} {T : List ℤ} (h : TrieMem μ tr cap fp T)
    (hs : SameOn (fun b => Inside tr cap b ∨ b = fp) μ μ' := by light_keep) :
    TrieMem μ' tr cap fp T :=
  have hle := h.le_cap
  ⟨h.seg.keep, (hs fp (.inr rfl)).trans h.free, hle, h.fp_out⟩

/-- The memory μ' agrees with μ outside the trie area and the cell fp. -/
abbrev SameOutsideTrie (μ μ' : ℕ → ℤ) (tr cap fp : ℕ) : Prop :=
  SameOn (fun b => Outside tr cap b ∧ b ≠ fp) μ μ'

/-! ## Procedure numbers

The numbers 0 to 39 belong to Section 2, the numbers from 40 on to Section 4. This file fixes 40 to
53; the files of the other routines of Section 4 fix theirs. -/

namespace Proc
/-- The numbers of the fourteen routines, in the order in which they call each other. -/
abbrev nineFirst : ℕ := 40
@[inherit_doc nineFirst] abbrev nineNext : ℕ := 41
@[inherit_doc nineFirst] abbrev scatter : ℕ := 42
@[inherit_doc nineFirst] abbrev starFirst : ℕ := 43
@[inherit_doc nineFirst] abbrev horner : ℕ := 44
@[inherit_doc nineFirst] abbrev lookup : ℕ := 45
@[inherit_doc nineFirst] abbrev insert : ℕ := 46
@[inherit_doc nineFirst] abbrev newRoot : ℕ := 47
@[inherit_doc nineFirst] abbrev sumTen : ℕ := 48
@[inherit_doc nineFirst] abbrev fillList : ℕ := 49
@[inherit_doc nineFirst] abbrev tile : ℕ := 50
@[inherit_doc nineFirst] abbrev allTiles : ℕ := 51
@[inherit_doc nineFirst] abbrev outDigits : ℕ := 52
@[inherit_doc nineFirst] abbrev queryCore : ℕ := 53
end Proc

/-! ## Time functions -/

/-- The routines with one loop over a string of n or L digits: a constant number of steps for each
digit. -/
def tNineFirst (n : ℕ) : ℕ := 30 * n + 30
@[inherit_doc tNineFirst] def tNineNext (n : ℕ) : ℕ := 90 * n + 60
@[inherit_doc tNineFirst] def tScatter (L : ℕ) : ℕ := 60 * L + 30
@[inherit_doc tNineFirst] def tStarFirst (L : ℕ) : ℕ := 50 * L + 30
@[inherit_doc tNineFirst] def tHorner (L : ℕ) : ℕ := 20 * L + 10
@[inherit_doc tNineFirst] def tLookup (L : ℕ) : ℕ := 20 * L + 12
@[inherit_doc tNineFirst] def tInsert (L : ℕ) : ℕ := 220 * L + 20
/-- Eleven cells are cleared. -/
def tNewRoot : ℕ := 160
/-- Ten times: write a digit, look up, add. -/
def tSumTen (L : ℕ) : ℕ := 10 * (tLookup L + 40) + 30
/-- A round for one box: stars, value (both branches are paid for), insertion, next leaf. -/
def tFillRound (L : ℕ) : ℕ :=
  tStarFirst L + tHorner L + tSumTen L + tInsert L + tNineNext L + 116
/-- One box: the test of the loop and a round. -/
def tFillStep (L : ℕ) : ℕ := tFillRound L + 4
/-- The boxes with a given number of stars, cnt of them. -/
def tFillList (L cnt : ℕ) : ℕ := tNineFirst L + cnt * tFillStep L + 60
/-- The trie of a tile: its root, then the boxes with 0, …, m - t stars. -/
def tTile (L m t : ℕ) : ℕ :=
  tNewRoot + ((List.range (m - t + 1)).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
    + 60
/-- All tiles. -/
def tAllTiles (L m t nB : ℕ) : ℕ := nB * (nB * (tTile L m t + 80) + 40) + 30
@[inherit_doc tNineFirst] def tOutDigits (L : ℕ) : ℕ := 70 * L + 40
/-- A query, once the digits of its output string are known. -/
def tQueryCore (L m t : ℕ) : ℕ :=
  2 * tNineFirst m + (lowList m t []).length * (tScatter L + tHorner L + tNineNext m + 90)
    + (boxesOf m t []).length * (tScatter L + tLookup L + tNineNext m + 90) + 120

/-! ## The enumeration of the strings with a bounded number of nines -/

/-- nineFirst(a, n, lo) writes the least string of n digits with lo nines. -/
def NineFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo : ℕ) (μ : ℕ → ℤ), lo ≤ n → a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineFirst d [a, n, lo] μ (tNineFirst n) fun _ μ' =>
      SegN μ' a (nineFirst n lo) ∧ SameOutside μ μ' a n

/-- nineNext(a, n, lo, hi) replaces the string at a by the next one and returns 1, or leaves it and
returns 0 if it is the last one. -/
def NineNextSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l ∈ nineStrs n lo hi →
    a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineNext d [a, n, lo, hi] μ (tNineNext n) fun r μ' =>
      SegN μ' a ((nineNext lo hi l).getD l) ∧ r = (if (nineNext lo hi l).isSome then 1 else 0) ∧
        SameOutside μ μ' a n

/-! ## Strings -/

/-- scatter(w, s, out, L, star) writes at out the string at w with its nines replaced by the digits
of the string at s, whose leading nines are first turned into stars if star = 1. -/
def ScatterSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (w s out L : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ), SegN μ w wl → SegN μ s sl →
    wl.length = L → sl.length = wl.count 9 → Apart out L w L → Apart out L s sl.length →
    w + L < lim.space → s + sl.length < lim.space → out + L < lim.space →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.scatter d [w, s, out, L, if star then 1 else 0] μ (tScatter L) fun _ μ' =>
      SegN μ' out (scatter wl (starRunIf star sl)) ∧ SameOutside μ μ' out L

/-- starFirst(cur, box, L, e) writes at box the string at cur with its first e nines turned into
stars; it returns the position of the last star (0 if e = 0). -/
def StarFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (cur box L e : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ cur l → l.length = L → Apart box L cur L →
    cur + L < lim.space → box + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.starFirst d [cur, box, L, e] μ (tStarFirst L) fun r μ' =>
      SegN μ' box (starFirst e l) ∧ r = ((lastStar (starFirst e l)).getD 0 : ℕ) ∧
        SameOutside μ μ' box L

/-- horner(a, L) returns the number with the L decimal digits at a, most significant first. -/
def HornerSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a L : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l.length = L → (∀ d ∈ l, d < 10) →
    a + L < lim.space →
    (10 : ℤ) ^ L ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.horner d [a, L] μ (tHorner L) fun r μ' => r = (ofDigitList 10 l : ℕ) ∧
      μ' = μ

/-! ## Tries -/

/-- lookup(tr, root, key, L) returns the value stored for the string at key in the trie with the
given root. -/
def LookupSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (tr root key L : ℕ) (T : List ℤ) (kl : List ℕ) (μ : ℕ → ℤ), Seg μ tr T → SegN μ key kl →
    kl.length = L →
    (∀ d ∈ kl, d < 11) → WalkOK T root kl → tr + T.length < lim.space → key + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.lookup d [tr, root, key, L] μ (tLookup L) fun r μ' =>
      r = trieLookup T root kl ∧ μ' = μ

/-- The arguments of insert(tr, root, key, L, val, fp), and the data behind them: the trie area of
cap cells at tr holds the array T, the cell fp holds its length, and the string kl is at key. -/
structure InsertArgs where
  (tr root key L : ℕ) (val : ℤ) (fp : ℕ)
  (cap : ℕ) (T : List ℤ) (kl : List ℕ)

/-- The values of the arguments of `insert`. -/
abbrev InsertArgs.vals (x : InsertArgs) : List ℤ := [x.tr, x.root, x.key, x.L, x.val, x.fp]

/-- What `insert` assumes: the tries and the string are in the memory, the walk down the string is
safe, there is room for one new vertex at each level, the string lies apart from the trie area and
from the free pointer, and everything lies within the memory. -/
structure InsertPre (lim : Limits) (μ : ℕ → ℤ) (x : InsertArgs) : Prop where
  trie : TrieMem μ x.tr x.cap x.fp x.T
  seg : SegN μ x.key x.kl
  len : x.kl.length = x.L
  digits : ∀ d ∈ x.kl, d < 11
  walk : InsertOK x.T x.root x.kl
  room : x.T.length + 11 * x.kl.length ≤ x.cap
  apart : Apart x.key x.kl.length x.tr x.cap := by light_arith
  free_out : Outside x.key x.kl.length x.fp := by light_arith
  area_in : x.tr + x.cap < lim.space := by light_arith
  key_in : x.key + x.kl.length < lim.space := by light_arith
  free_in : x.fp < lim.space := by light_arith

/-- insert(tr, root, key, L, val, fp) stores val for the string at key in the trie with the given
root. A new vertex is taken from the free part of the trie area, and its eleven cells are
cleared. -/
def InsertSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : InsertArgs) (μ : ℕ → ℤ), InsertPre lim μ x →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.insert d x.vals μ (tInsert x.L) fun _ μ' =>
      TrieMem μ' x.tr x.cap x.fp (trieInsert x.T x.root x.kl x.val) ∧
        SameOutsideTrie μ μ' x.tr x.cap x.fp

/-- newRoot(tr, fp) takes a new vertex from the free part of the trie area, clears its eleven cells,
and returns its address. -/
def NewRootSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (tr cap fp : ℕ) (T : List ℤ) (μ : ℕ → ℤ), TrieMem μ tr cap fp T → T.length + 11 ≤ cap →
    tr + cap < lim.space →
    fp < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.newRoot d [tr, fp] μ tNewRoot fun r μ' =>
      r = T.length ∧ TrieMem μ' tr cap fp (trieNew T) ∧ SameOutsideTrie μ μ' tr cap fp

/-! ## The dynamic program of Lemma 29 -/

/-- The arguments of sumTen(tr, root, box, L, p), and the data behind them: the array T of the tries
is at tr, and the string l, which has a star at the position p, is at box. -/
structure SumTenArgs where
  (tr root box L p : ℕ)
  (T : List ℤ) (l : List ℕ)

/-- The values of the arguments of `sumTen`. -/
abbrev SumTenArgs.vals (x : SumTenArgs) : List ℤ := [x.tr, x.root, x.box, x.L, x.p]

/-- The ten values that `sumTen` adds up. -/
abbrev SumTenArgs.values (x : SumTenArgs) : List ℤ := tenValues (trieLookup x.T x.root) x.l x.p

/-- What `sumTen` assumes: the array of the tries and the box, which do not meet and lie within the
memory, the position of the star, that the ten strings are stored, and that the partial sums of
their values fit in a word. -/
structure SumTenPre (lim : Limits) (μ : ℕ → ℤ) (x : SumTenArgs) : Prop where
  area : Seg μ x.tr x.T
  seg : SegN μ x.box x.l
  len : x.l.length = x.L
  star : x.p < x.l.length
  digits : ∀ d ∈ x.l, d < 11
  walk : ∀ d < 10, WalkOK x.T x.root (x.l.set x.p d)
  sums : ∀ j ≤ 10, |(x.values.take j).sum| ≤ lim.word
  apart : Apart x.box x.l.length x.tr x.T.length := by light_arith
  area_in : x.tr + x.T.length < lim.space := by light_arith
  box_in : x.box + x.l.length < lim.space := by light_arith

/-- sumTen(tr, root, box, L, p) returns the sum of the ten values, looked up in the trie with the
given root, of the strings obtained from the string at box by writing 0, …, 9 at the position p; it
leaves the memory as it was. -/
def SumTenSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : SumTenArgs) (μ : ℕ → ℤ), SumTenPre lim μ x →
    ∀ d, d + 1 ≤ lim.depth → Meets lim P Proc.sumTen d x.vals μ (tSumTen x.L) fun r μ' =>
      r = x.values.sum ∧ μ' = μ

/-- What the routines for a tile assume about their surroundings: the parameters, the two encodings
of the tile and where they are, the trie area, two scratch strings, and the limits. -/
structure TileCtx (lim : Limits) (L m t : ℕ) (encA encB : Leaf L → ℤ)
    (aA aB tr cap fp cur box : ℕ) : Prop where
  std : Std lim
  ht : t ≤ m
  hmL : m ≤ L
  /-- Every value and every partial sum fits in a word. -/
  value_le : ∃ A B : ℤ, (∀ τ, |encA τ| ≤ A) ∧ (∀ τ, |encB τ| ≤ B) ∧ 10 ^ m * (A * B) ≤ lim.word
  pow_le : (10 : ℤ) ^ L ≤ lim.word
  /-- The two encodings, the two scratch strings, the cell fp and the trie area lie in this order,
  and the last cell of the memory lies behind them. -/
  layout : InOrder (lim.space - 1)
    [(aA, 10 ^ L), (aB, 10 ^ L), (cur, L), (box, L), (fp, 1), (tr, cap)]

/-- The memory μ' agrees with μ outside the trie area, the cell fp, and the two scratch strings. -/
abbrev SameOutsideTile (μ μ' : ℕ → ℤ) (L tr cap fp cur box : ℕ) : Prop :=
  SameOn (fun b => Outside tr cap b ∧ b ≠ fp ∧ Outside cur L b ∧ Outside box L b) μ μ'

/-- The arguments of fillList(e, root, aA, aB, tr, fp, cur, box, L, mt), with mt = m - t, and the
data behind them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap
cells at tr holds the array T, and fp holds its length; cur and box (L cells each) are scratch. The
array is described as in `fillTrie_rep`: tile is the number of the trie (the number of the tile),
roots tile its root, old what the other tries hold, and lo the address from which the tries stand
in the array. -/
structure FillListArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box e tile lo : ℕ)
  roots : ℕ → ℕ
  old : ℕ × List ℕ → Option ℤ
  T : List ℤ

namespace FillListArgs

variable (x : FillListArgs)

/-- The root of the trie of the tile. -/
abbrev root : ℕ := x.roots x.tile

/-- The values of the arguments of `fillList`. -/
abbrev vals : List ℤ :=
  [x.e, x.root, x.aA, x.aB, x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ)]

/-- The boxes that `fillList` inserts. -/
abbrev boxes : List (List ℕ) := starBoxes x.L x.m x.t x.e

/-- What the tries hold when the boxes in pre have been inserted. -/
abbrev stored (pre : List (List ℕ)) : ℕ × List ℕ → Option ℤ :=
  storedUpTo x.old x.tile (arrT x.encA) (arrT x.encB) x.L x.m x.t x.e pre

end FillListArgs

/-- The arguments of tile(aA, aB, ra, tr, fp, cur, box, L, mt), with mt = m - t, and the data behind
them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap cells at tr
holds the tries s.cells of the earlier tiles, in which the values old are stored, and fp holds their
length; their roots s.roots, one for each tile, are in the cells from aR, and ra is the address of
the cell behind them; cur and box (L cells each) are scratch; the tries stand in the trie array from
the address lo on. -/
structure TileArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box aR : ℕ)
  s : TrieStore
  old : ℕ × List ℕ → Option ℤ
  lo : ℕ

/-- The trie array and the roots after the trie of the tile has been built. -/
def TileArgs.tries (x : TileArgs) : TrieStore :=
  tileTrie (arrT x.encA) (arrT x.encB) x.L x.m x.t x.s

/-- The number of cells for the roots, the older ones and the new one. -/
def TileArgs.cells (x : TileArgs) : ℕ := x.s.roots.length + 1

/-- The cells that `tile` keeps: those outside the trie area, the cell fp, the two scratch strings
and the cell of the new root. -/
abbrev TileArgs.Kept (x : TileArgs) (b : ℕ) : Prop :=
  Outside x.tr x.cap b ∧ b ≠ x.fp ∧ Outside x.cur x.L b ∧ Outside x.box x.L b ∧
    b ≠ x.aR + x.s.roots.length

/-- The arguments of allTiles(aENCA, aENCB, nB, T, aR, tr, fp, cur, box, L, mt), with T = 10^L and
mt = m - t, and the data behind them: the encodings of the nB row bands from aENCA and of the nB
column bands from aENCB (band β at the offset β 10^L), the cells of the roots from aR (one for each
tile), the trie area of cap cells from tr, the cell fp for its length, and two scratch strings cur
and box. -/
structure AllTilesArgs where
  (L m t nB : ℕ)
  (encA encB : ℕ → Leaf L → ℤ)
  (aENCA aENCB aR tr cap fp cur box : ℕ)

/-- The tries of all tiles, and their roots. -/
def AllTilesArgs.tries (x : AllTilesArgs) : TrieStore :=
  allTries x.L x.m x.t (tileList x.nB x.encA x.encB)

/-- The cells that `allTiles` keeps: those below cur and those behind the trie area. -/
abbrev AllTilesArgs.Kept (x : AllTilesArgs) (b : ℕ) : Prop := b < x.cur ∨ x.tr + x.cap ≤ b

/-! ## A query -/

/-- The arguments of outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) and the data behind them: gI and gJ
are the numbers of the blocks of I and J within their bands, dI and dJ the addresses of the base-3
digits rI and rJ of their offsets, aMASK the address of the list of the subsets (a mask of L cells
for each), k0 the number of blocks of a band, L the number of levels, m of which belong to a subset,
and wd the address of the result. -/
structure OutDigitsArgs where
  (gI gJ dI dJ aMASK k0 L wd m : ℕ)
  (rI rJ : List ℕ)

namespace OutDigitsArgs

variable (x : OutDigitsArgs)

/-- The mask of the subset of the block product (gI, gJ). -/
def mask : List Bool := unrank x.L x.m (x.gI * x.k0 + x.gJ)

/-- The address of that mask in the list of the subsets. -/
def base : ℕ := x.aMASK + (x.gI * x.k0 + x.gJ) * x.L

/-- The digits of the output string: 9 at the levels of the subset, and elsewhere 3 a + b for the
next digits a of rI and b of rJ. -/
def digits : List ℕ := outDigits x.m x.mask x.rI x.rJ

end OutDigitsArgs

/-- What `outDigits` assumes: the mask of the subset and the digits of the two offsets stand in the
memory, and the L cells from wd are apart from all three. -/
structure OutDigitsPre (lim : Limits) (μ : ℕ → ℤ) (x : OutDigitsArgs) : Prop where
  std : Std lim
  m_le : x.m ≤ x.L
  gI_lt : x.gI < x.k0
  gJ_lt : x.gJ < x.k0
  index_lt : x.gI * x.k0 + x.gJ < x.L.choose x.m
  segMask : SegN μ x.base (x.mask.map fun b => if b then 1 else 0)
  segI : SegN μ x.dI x.rI
  segJ : SegN μ x.dJ x.rJ
  lenI : x.rI.length = x.L - x.m
  lenJ : x.rJ.length = x.L - x.m
  ltI : ∀ a ∈ x.rI, a < 3
  ltJ : ∀ a ∈ x.rJ, a < 3
  apartMask : Apart x.wd x.L x.base x.L
  apartI : Apart x.wd x.L x.dI (x.L - x.m)
  apartJ : Apart x.wd x.L x.dJ (x.L - x.m)
  spaceMasks : x.aMASK + x.k0 * x.k0 * x.L < lim.space
  spaceI : x.dI + x.L < lim.space
  spaceJ : x.dJ + x.L < lim.space
  spaceDest : x.wd + x.L < lim.space

/-- `outDigits` writes the digits of the output string at wd and changes nothing else. -/
def OutDigitsSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : OutDigitsArgs) (μ : ℕ → ℤ), OutDigitsPre lim μ x →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.outDigits d [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd] μ
      (tOutDigits x.L) fun _ μ' => SegN μ' x.wd x.digits ∧ SameOutside μ μ' x.wd x.L

/-- The arguments of queryCore(aA, aB, tr, root, wd, ss, box, L, m, t) and the data behind them: the
encodings encA and encB of the tile are at aA and aB, the trie array T at tr, root is the root of
the trie of the tile, the digits of the output string η are at wd; ss (m cells) and box (L cells)
are scratch. -/
structure QueryCoreArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  η : OutStr L
  (aA aB tr root wd ss box : ℕ)
  T : List ℤ

/-- The numbers that the query adds up, in the order in which it adds them. -/
def QueryCoreArgs.terms (x : QueryCoreArgs) : List ℤ :=
  queryTerms x.m x.t (arrT x.encA) (arrT x.encB) (trieLookup x.T x.root) (digitsO x.η)

end Light.Sec4
