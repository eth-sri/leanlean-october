module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics

/-!
# Sorting on the RAM, part 1: the list model (WP-C)

The mathematical model of the bottom-up merge sort run by the RAM program of
`Chazelle.Core.SortRam`:

* `seg m a n`: the list of the `n` memory words `m a, m (a + 1), …, m (a + n - 1)`; the lemmas
  `seg_succ`, `seg_add`, `seg_snoc`, `seg_drop`, `seg_congr` describe how it changes with the
  memory and the bounds;
* `mpass le w l`: one pass of the bottom-up merge sort (merge the blocks `[2tw, 2tw + w)` and
  `[2tw + w, 2tw + 2w)` for every `t`), defined with `List.merge`;
* `ChunkSorted le w l`: every block `[tw, tw + w)` of `l` is sorted.

Main facts: a pass is a permutation (`mpass_perm`), preserves the length (`mpass_length`), and
turns `w`-sorted lists into `2w`-sorted lists (`chunkSorted_mpass`) for a transitive total
`le`; a list of length `≤ w` that is `w`-sorted is sorted (`pairwise_of_chunkSorted`).
`mpass_append` and `mpass_small` describe a pass block by block, as the RAM computes it.
-/

namespace Chazelle.Core.SortL

@[expose] public section

/-! ## Memory segments -/

/-- The memory segment of length `n` at `a`, as a list. -/
def seg (m : ℕ → ℕ) (a n : ℕ) : List ℕ := (List.range n).map fun i => m (a + i)

variable {m m' : ℕ → ℕ} {a n : ℕ}

/-- A segment has the requested length. -/
@[simp] theorem seg_length : (seg m a n).length = n := by simp [seg]

/-- The empty segment. -/
@[simp] theorem seg_zero : seg m a 0 = [] := rfl

/-- Reading a segment from its first word. -/
theorem seg_succ : seg m a (n + 1) = m a :: seg m (a + 1) n := by
  unfold seg
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  congr 1
  omega

/-- A segment splits at any point. -/
theorem seg_add (n₁ n₂ : ℕ) : seg m a (n₁ + n₂) = seg m a n₁ ++ seg m (a + n₁) n₂ := by
  induction n₁ generalizing a with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + n₂ = (k + n₂) + 1 by omega, seg_succ, ih, seg_succ,
      show a + 1 + k = a + (k + 1) by omega]
    simp only [List.cons_append]

/-- Reading a segment from its last word. -/
theorem seg_snoc : seg m a (n + 1) = seg m a n ++ [m (a + n)] := by
  rw [seg_add n 1, seg_succ]
  simp

/-- Segments agree when the memories agree on them. -/
theorem seg_congr (h : ∀ i, i < n → m (a + i) = m' (a + i)) : seg m a n = seg m' a n := by
  unfold seg
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.1 hi)

/-- Dropping the first words of a segment. -/
theorem seg_drop (d : ℕ) : (seg m a n).drop d = seg m (a + d) (n - d) := by
  induction d generalizing a n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [seg_succ, List.drop_succ_cons, ih]
      congr 1
      · omega
      · omega

/-- Taking the first words of a segment. -/
theorem seg_take (d : ℕ) : (seg m a n).take d = seg m a (min d n) := by
  induction d generalizing a n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [seg_succ, List.take_succ_cons, ih, show min (k + 1) (n + 1) = min k n + 1 by omega,
        seg_succ]

/-- The words of a segment. -/
theorem seg_getD (i : ℕ) (hi : i < n) : (seg m a n).getD i 0 = m (a + i) := by
  simp [seg, hi]

/-- A segment written one word past its end. -/
theorem seg_upd_end (v : ℕ) (f : ℕ → ℕ)
    (hf : ∀ x, f x = if x = a + n then v else m x) :
    seg f a (n + 1) = seg m a n ++ [v] := by
  rw [seg_snoc, hf (a + n), ite_eq_left rfl]
  congr 1
  apply seg_congr
  intro i hi
  simp only [hf]
  rw [ite_eq_right_iff]
  intro h
  omega

/-! ## One pass of the bottom-up merge sort -/

variable {α : Type} (le : α → α → Bool)

/-- **One merge pass** with run width `w`: merge the blocks `[2tw, 2tw + w)` and
`[2tw + w, 2tw + 2w)`, for `t = 0, 1, …`. -/
def mpass (w : ℕ) (l : List α) : List α :=
  if _h : w = 0 ∨ l = [] then l
  else List.merge (l.take w) ((l.drop w).take w) le ++ mpass w (l.drop (2 * w))
termination_by l.length
decreasing_by
  simp only [not_or] at _h
  have h1 : l.length ≠ 0 := by simpa using _h.2
  simp only [List.length_drop]
  omega

variable {le}

/-- A pass of width `0` does nothing. -/
theorem mpass_zero (l : List α) : mpass le 0 l = l := by
  rws [mpass]

/-- A pass of the empty list. -/
theorem mpass_nil (w : ℕ) : mpass le w ([] : List α) = [] := by
  rws [mpass]

/-- The defining equation of a pass on a nonempty list. -/
theorem mpass_eq {w : ℕ} {l : List α} (hw : 0 < w) (hl : l ≠ []) :
    mpass le w l = List.merge (l.take w) ((l.drop w).take w) le ++ mpass le w (l.drop (2 * w)) := by
  rw [mpass, dite_eq_right_iff.mpr]
  intro h
  rcases h with h | h
  · omega
  · exact absurd h hl

/-- A list is its first block, its second block and the rest. -/
theorem take_append_take_drop (w : ℕ) (l : List α) :
    l.take w ++ (l.drop w).take w ++ l.drop (2 * w) = l := by
  rw [List.append_assoc, show 2 * w = w + w by omega, ← List.drop_drop, List.take_append_drop,
    List.take_append_drop]

/-- **A pass is a permutation.** -/
theorem mpass_perm (w : ℕ) (l : List α) : (mpass le w l).Perm l := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rw [mpass_zero]
    by_cases hl : l = []
    · subst hl; rw [mpass_nil]
    rw [mpass_eq hw hl]
    have hlen : (l.drop (2 * w)).length < n := by
      have : l.length ≠ 0 := by simpa using hl
      sio only [List.length_drop]
    have h1 := (List.merge_perm_append le (xs := l.take w) (ys := (l.drop w).take w)).append
      (ih _ hlen (l.drop (2 * w)) rfl)
    exact h1.trans (by rw [take_append_take_drop])

/-- The first block of a pass has length `min (2 w) |l|`. -/
theorem merge_block_length (w : ℕ) (l : List α) :
    (List.merge (l.take w) ((l.drop w).take w) le).length = min (2 * w) l.length := by
  rw [List.length_merge]
  simp only [List.length_take, List.length_drop]
  omega

/-- **A pass works block by block**: a prefix made of whole double blocks is passed
separately. -/
theorem mpass_append {w : ℕ} (hw : 0 < w) (t : ℕ) (l₁ l₂ : List α)
    (h : l₁.length = t * (2 * w)) : mpass le w (l₁ ++ l₂) = mpass le w l₁ ++ mpass le w l₂ := by
  induction t generalizing l₁ with
  | zero =>
    simp only [Nat.zero_mul, List.length_eq_zero_iff] at h
    subst h
    simp [mpass_nil]
  | succ t ih =>
    have h2w : 2 * w ≤ l₁.length := by
      rw [h]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos t)
    have hl₁ : l₁ ≠ [] := by
      intro h'; subst h'; sio at h2w
    have hl : l₁ ++ l₂ ≠ [] := by simp [hl₁]
    rw [mpass_eq hw hl, mpass_eq hw hl₁]
    have ht1 : (l₁ ++ l₂).take w = l₁.take w := by
      rw [List.take_append_of_le_length (by omega)]
    have ht2 : ((l₁ ++ l₂).drop w).take w = (l₁.drop w).take w := by
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by sio only [List.length_drop])]
    have ht3 : (l₁ ++ l₂).drop (2 * w) = l₁.drop (2 * w) ++ l₂ := by
      rw [List.drop_append_of_le_length (by omega)]
    rw [ht1, ht2, ht3, ih _ (by simp only [List.length_drop]; rwo [h, Nat.succ_mul]),
      List.append_assoc]

/-- A list of at most two blocks is passed by one merge. -/
theorem mpass_small {w : ℕ} (hw : 0 < w) (l : List α) (hl : l.length ≤ 2 * w) :
    mpass le w l = List.merge (l.take w) (l.drop w) le := by
  by_cases hne : l = []
  · subst hne; simp [mpass_nil]
  rw [mpass_eq hw hne, List.drop_of_length_le hl, mpass_nil, List.append_nil,
    List.take_of_length_le (l := l.drop w) (by sio only [List.length_drop])]

/-- Dropping whole double blocks commutes with a pass. -/
theorem mpass_drop {w : ℕ} (hw : 0 < w) (t : ℕ) (l : List α) :
    (mpass le w l).drop (t * (2 * w)) = mpass le w (l.drop (t * (2 * w))) := by
  induction t generalizing l with
  | zero => simp
  | succ t ih =>
    by_cases hne : l = []
    · subst hne; simp [mpass_nil]
    rw [mpass_eq hw hne]
    have hB := merge_block_length (le := le) w l
    have e1 : (t + 1) * (2 * w) = 2 * w + t * (2 * w) := by ring
    by_cases hlen : 2 * w ≤ l.length
    · rw [e1, ← List.drop_drop, List.drop_left' (by rwo [hB]), ih, List.drop_drop]
    · have h1 : l.drop (2 * w) = [] := List.drop_of_length_le (by omega)
      rw [h1, mpass_nil, List.append_nil, List.drop_of_length_le (by rwo [hB]),
        List.drop_of_length_le (l := l) (by omega), mpass_nil]

/-- The first double block of a pass. -/
theorem take_mpass {w : ℕ} (hw : 0 < w) (l : List α) :
    (mpass le w l).take (2 * w) = List.merge (l.take w) ((l.drop w).take w) le := by
  by_cases hne : l = []
  · subst hne; simp [mpass_nil]
  rw [mpass_eq hw hne]
  have hB := merge_block_length (le := le) w l
  by_cases hlen : 2 * w ≤ l.length
  · rw [List.take_left' (by rwo [hB])]
  · have h1 : l.drop (2 * w) = [] := List.drop_of_length_le (by omega)
    rw [h1, mpass_nil, List.append_nil, List.take_of_length_le (by rwo [hB])]

/-! ## Sorted blocks -/

/-- Every block `[t w, t w + w)` of `l` is sorted. -/
def ChunkSorted (le : α → α → Bool) (w : ℕ) (l : List α) : Prop :=
  ∀ t, ((l.drop (t * w)).take w).Pairwise fun a b => le a b

/-- Blocks of width `1` are sorted. -/
theorem chunkSorted_one (l : List α) : ChunkSorted le 1 l := by
  intro t
  rcases (l.drop (t * 1)) with _ | ⟨x, xs⟩
  · simp
  · simp

/-- **A pass doubles the width of the sorted blocks** (for a transitive total order). -/
theorem chunkSorted_mpass (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) {w : ℕ} (hw : 0 < w) {l : List α}
    (h : ChunkSorted le w l) : ChunkSorted le (2 * w) (mpass le w l) := by
  intro t
  rw [mpass_drop hw, take_mpass hw]
  apply List.pairwise_merge trans total
  · have := h (2 * t)
    rwa [show 2 * t * w = t * (2 * w) by ring] at this
  · have := h (2 * t + 1)
    rwa [show (2 * t + 1) * w = t * (2 * w) + w by ring, ← List.drop_drop] at this

/-- A `w`-sorted list of length at most `w` is sorted. -/
theorem pairwise_of_chunkSorted {w : ℕ} {l : List α} (h : ChunkSorted le w l)
    (hl : l.length ≤ w) : l.Pairwise fun a b => le a b := by
  have := h 0
  rwa [Nat.zero_mul, List.drop_zero, List.take_of_length_le hl] at this

/-! ## One step of a merge -/

/-- Taking the head of the left list in a merge. -/
theorem merge_step_left {out a b xs ys : List α} {x : α}
    (h : out ++ List.merge (x :: xs) ys le = List.merge a b le)
    (hxy : ∀ y ys', ys = y :: ys' → le x y) :
    (out ++ [x]) ++ List.merge xs ys le = List.merge a b le := by
  rw [← h]
  cases ys with
  | nil => simp
  | cons y ys' => rws [List.cons_merge_cons_pos _ _ _ (hxy y ys' rfl)]

/-- Taking the head of the right list in a merge. -/
theorem merge_step_right {out a b xs ys : List α} {y : α}
    (h : out ++ List.merge xs (y :: ys) le = List.merge a b le)
    (hxy : ∀ x xs', xs = x :: xs' → ¬ le x y) :
    (out ++ [y]) ++ List.merge xs ys le = List.merge a b le := by
  rw [← h]
  cases xs with
  | nil => simp
  | cons x xs' => rws [List.cons_merge_cons_neg _ _ _ (hxy x xs' rfl)]

end

end Chazelle.Core.SortL
