module

public import Chazelle.Final.Wedge
public import Chazelle.Split.Multi
public import Chazelle.Final.Degree

/-!
# Splitting a simple polygon along its diagonal list with a linked structure

This file gives the abstract (list-level) version of the linear-time splitting of a simple
polygon `P` along a list `D` of non-crossing diagonals, and proves it correct against
`Chazelle.Split.splitAll`.

## Sequential splitting (`seqSplit`)

`cut P pcs d` replaces every piece `m` of the list `pcs` in which `d` is an interior diagonal
(`IsDiag P m d`) by its two pieces `splitFst m d`, `splitSnd m d`; `seqSplit P pcs D` cuts
along the members of `D` in order.  `seqSplit_eq_splitAll`: for a diagonal system,
`seqSplit P [l] D = splitAll l D` (the recursion of `splitAll` distributes the remaining
diagonals exactly as sequential cutting does).  `Good P σ pcs E` is the invariant of sequential
cutting: simple pieces of orientation `σ` with pairwise disjoint interiors, every remaining
diagonal an interior diagonal of some piece, the remaining diagonals pairwise non-crossing.

## The linked structure (`LState`)

Pieces are cycles of *nodes*; a node is a copy of a vertex: `vtx z` is its vertex, `nxt z`,
`prv z` its neighbours in its cycle, `cnt` the number of nodes (`0 … cnt - 1`), `cop v` the list
of the copies of the vertex `v`.  Initially node `i` is vertex `i` (`init n`).

`step P σ S (a, b)`: the copy `x` of `a` whose corner passes the wedge test towards `b`
(`nodeWedge`, `Chazelle.Final.wedgeTest` with the corner `vtx (prv x) → a → vtx (nxt x)`), the
copy `y` of `b` whose corner passes the wedge test towards `a`, two new nodes `x' = cnt` (a copy of
`a`) and `y' = cnt + 1` (a copy of `b`), and the surgery

```
nxt y := x, prv x := y                       -- first cycle  x → … → y → x
nxt y' := nxt y, prv (nxt y) := y',          -- second cycle y' → nxt y → … → prv x → x' → y'
nxt (prv x) := x', prv x' := prv x, nxt x' := y', prv y' := x'
```

`Repr S cs`: the node lists `cs` partition `0 … cnt - 1` into cycles of `S`, and `cop` lists the
copies.  **Main theorem** (`runState_spec`): for an enumeration `D` of the inserted diagonals,
after processing `D` from `init P.n` with `σ = orient P`, the cycles read as vertex lists are a
permutation of the pieces `splitAll (List.range P.n) D` (exactly, each cycle read from the right
node).  Consequences: every cycle read from any of its nodes is a piece (`IsPiece`), and the
triangulations of the cycles assemble into a triangulation of `P` (`triangulates_of_cycles`).

## Cost

Processing `(a, b)` performs at most `(cop a).length + (cop b).length` wedge tests; the copies of
a vertex `v` number `1 +` (the processed diagonals incident to `v`), at most `11` for
`diagList P T C` (`countP_diagList_le`), so the total number of wedge tests is at most
`22 * D.length` (`runCost_le`).
-/

namespace Chazelle.Final

@[expose] public section

open Set
open Chazelle.Split (IsDiag NonCross splitFst splitSnd splitAll splitAll_nil splitAll_cons
  diagsFst diagsSnd sideTest sideTest_eq_true DiagSystem mem_of_mem_arcList EnumDiags
  splitPair_split SplitPair)
open Chazelle.EarClip (subPoly n_subPoly subPoly_range)
open Chazelle.Mountain (orient orient_eq IsPiece)

variable {P : Polygon}

/-! ### Sequential cutting -/

open Classical in
/-- Cut every piece of `pcs` in which `d` is an interior diagonal into its two pieces. -/
noncomputable def cut (P : Polygon) (pcs : List (List ℕ)) (d : ℕ × ℕ) : List (List ℕ) :=
  pcs.flatMap fun m => if IsDiag P m d then [splitFst m d, splitSnd m d] else [m]

/-- Cut along the members of `D` in order. -/
noncomputable def seqSplit (P : Polygon) : List (List ℕ) → List (ℕ × ℕ) → List (List ℕ)
  | pcs, [] => pcs
  | pcs, d :: D => seqSplit P (cut P pcs d) D

@[simp] theorem seqSplit_nil (pcs : List (List ℕ)) : seqSplit P pcs [] = pcs := rfl

theorem seqSplit_cons (pcs : List (List ℕ)) (d : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    seqSplit P pcs (d :: D) = seqSplit P (cut P pcs d) D := rfl

theorem cut_append (A B : List (List ℕ)) (d : ℕ × ℕ) :
    cut P (A ++ B) d = cut P A d ++ cut P B d := by
  unfold cut; rw [List.flatMap_append]

theorem cut_cons_of_isDiag {m : List ℕ} {rest : List (List ℕ)} {d : ℕ × ℕ} (h : IsDiag P m d) :
    cut P (m :: rest) d = splitFst m d :: splitSnd m d :: cut P rest d := by
  unfold cut; rw [List.flatMap_cons, ite_eq_left h]; rfl

theorem cut_cons_of_not_isDiag {m : List ℕ} {rest : List (List ℕ)} {d : ℕ × ℕ}
    (h : ¬ IsDiag P m d) : cut P (m :: rest) d = m :: cut P rest d := by
  unfold cut; rw [List.flatMap_cons, ite_eq_right h]; rfl

/-- Cutting along a diagonal of no piece changes nothing. -/
theorem cut_eq_self {pcs : List (List ℕ)} {d : ℕ × ℕ} (h : ∀ m ∈ pcs, ¬ IsDiag P m d) :
    cut P pcs d = pcs := by
  induction pcs with
  | nil => rfl
  | cons m rest ih =>
    rw [cut_cons_of_not_isDiag (h m List.mem_cons_self),
      ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')]

/-- Cutting respects permutations of the piece list. -/
theorem cut_perm {pcs pcs' : List (List ℕ)} (h : List.Perm pcs pcs') (d : ℕ × ℕ) :
    List.Perm (cut P pcs d) (cut P pcs' d) :=
  List.Perm.flatMap_right _ h

/-- A member of a cut is a piece of the list or one of its two pieces along `d`. -/
theorem mem_cut {pcs : List (List ℕ)} {d : ℕ × ℕ} {m' : List ℕ} (h : m' ∈ cut P pcs d) :
    ∃ m ∈ pcs, (IsDiag P m d ∧ (m' = splitFst m d ∨ m' = splitSnd m d)) ∨
      (¬ IsDiag P m d ∧ m' = m) := by
  unfold cut at h
  rw [List.mem_flatMap] at h
  obtain ⟨m, hm, h'⟩ := h
  refine ⟨m, hm, ?_⟩
  by_cases hd : IsDiag P m d
  · rw [ite_eq_left hd] at h'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    exact Or.inl ⟨hd, h'⟩
  · rw [ite_eq_right hd, List.mem_singleton] at h'
    exact Or.inr ⟨hd, h'⟩

theorem seqSplit_append (A B : List (List ℕ)) (D : List (ℕ × ℕ)) :
    seqSplit P (A ++ B) D = seqSplit P A D ++ seqSplit P B D := by
  induction D generalizing A B with
  | nil => rfl
  | cons d D ih => rw [seqSplit_cons, cut_append, ih]; rfl

/-- The entries of the pieces of a cut are entries of the pieces cut. -/
theorem sub_of_mem_cut {pcs : List (List ℕ)} {l' : List ℕ} (h : ∀ m ∈ pcs, ∀ x ∈ m, x ∈ l')
    {d : ℕ × ℕ} : ∀ m ∈ cut P pcs d, ∀ x ∈ m, x ∈ l' := by
  intro m' hm' x hx
  obtain ⟨m, hm, (⟨-, rfl | rfl⟩ | ⟨-, rfl⟩)⟩ := mem_cut hm'
  · exact h m hm x (mem_of_mem_arcList hx)
  · exact h m hm x (mem_of_mem_arcList hx)
  · exact h _ hm x hx

/-- **Irrelevant diagonals.**  When all entries of the pieces are entries of `l'`, the
diagonals without both endpoints in `l'` cut nothing. -/
theorem seqSplit_filter {pcs : List (List ℕ)} {l' : List ℕ} (h : ∀ m ∈ pcs, ∀ x ∈ m, x ∈ l')
    (D : List (ℕ × ℕ)) : seqSplit P pcs D = seqSplit P pcs (D.filter (sideTest l')) := by
  induction D generalizing pcs with
  | nil => rfl
  | cons d D ih =>
    by_cases hd : sideTest l' d = true
    · rw [List.filter_cons_of_pos hd, seqSplit_cons, seqSplit_cons, ih (sub_of_mem_cut h)]
    · rw [List.filter_cons_of_neg hd, seqSplit_cons, ih (sub_of_mem_cut h)]
      congr 1
      apply cut_eq_self
      intro m hm hdiag
      exact hd (sideTest_eq_true.2 ⟨h m hm _ hdiag.1, h m hm _ hdiag.2.1⟩)

/-- **Sequential cutting is `splitAll`.**  For a diagonal system `D` of `(P, l)`, cutting `[l]`
along the members of `D` in order gives exactly `splitAll l D`. -/
theorem seqSplit_eq_splitAll {l : List ℕ} {D : List (ℕ × ℕ)} (h : DiagSystem P l D) :
    seqSplit P [l] D = splitAll l D := by
  revert h
  refine Chazelle.Split.splitAll_induction (motive := fun l D => DiagSystem P l D →
    seqSplit P [l] D = splitAll l D) ?_ ?_ l D
  · intro l _; rw [splitAll_nil]; rfl
  · intro l d D ih₁ ih₂ h
    have hd := h.diag d List.mem_cons_self
    rw [seqSplit_cons, show cut P [l] d = [splitFst l d] ++ [splitSnd l d] from
      cut_cons_of_isDiag hd, seqSplit_append, splitAll_cons, ← ih₁ h.fst, ← ih₂ h.snd]
    have hsub₁ : ∀ m ∈ [splitFst l d], ∀ x ∈ m, x ∈ splitFst l d := by
      intro m hm x hx; rw [List.mem_singleton] at hm; rw [← hm]; exact hx
    have hsub₂ : ∀ m ∈ [splitSnd l d], ∀ x ∈ m, x ∈ splitSnd l d := by
      intro m hm x hx; rw [List.mem_singleton] at hm; rw [← hm]; exact hx
    congr 1
    · rw [seqSplit_filter hsub₁]; rfl
    · rw [seqSplit_filter hsub₂, seqSplit_filter hsub₂ (diagsSnd l d D)]
      congr 1
      unfold diagsSnd
      rw [List.filter_filter]
      apply List.filter_congr
      intro e he
      by_cases h2 : sideTest (splitSnd l d) e = true
      · have h1 : sideTest (splitFst l d) e = false := by
          by_contra h1
          rw [Bool.not_eq_false] at h1
          exact h.splitPair.not_mem_both h.simple (h.tail_isDiag he) (h.tail_nonCross he)
            (sideTest_eq_true.1 h1) (sideTest_eq_true.1 h2)
        rw [h1, h2]; rfl
      · rw [Bool.not_eq_true] at h2
        simp [h2]

/-! ### The invariant of sequential cutting -/

/-- **The invariant of sequential cutting**: the pieces are simple with orientation `σ` and
pairwise disjoint interiors; every remaining diagonal is an interior diagonal of some piece; the
remaining diagonals are pairwise non-crossing. -/
structure Good (P : Polygon) (σ : ℝ) (pcs : List (List ℕ)) (E : List (ℕ × ℕ)) : Prop where
  simple : ∀ m ∈ pcs, (subPoly P m).Simple
  orient : ∀ m ∈ pcs, orient (subPoly P m) = σ
  disj : pcs.Pairwise fun m m' =>
    Disjoint (interior (subPoly P m).filled) (interior (subPoly P m').filled)
  diag : ∀ e ∈ E, ∃ m ∈ pcs, IsDiag P m e
  noncross : E.Pairwise (NonCross P)

/-- The invariant is insensitive to the order of the pieces. -/
theorem Good.perm {σ : ℝ} {pcs pcs' : List (List ℕ)} {E : List (ℕ × ℕ)} (h : Good P σ pcs E)
    (hp : List.Perm pcs pcs') : Good P σ pcs' E where
  simple m hm := h.simple m (hp.mem_iff.2 hm)
  orient m hm := h.orient m (hp.mem_iff.2 hm)
  disj := hp.pairwise h.disj fun hd => hd.symm
  diag e he := by
    obtain ⟨m, hm, hd⟩ := h.diag e he
    exact ⟨m, hp.mem_iff.1 hm, hd⟩
  noncross := h.noncross

/-- The interior of a filled piece lies in the interior of the piece it was cut from. -/
theorem interior_subset_of_mem_cut {pcs : List (List ℕ)} {d : ℕ × ℕ}
    (hs : ∀ m ∈ pcs, (subPoly P m).Simple) {m' : List ℕ} (hm' : m' ∈ cut P pcs d) :
    ∃ m ∈ pcs, interior (subPoly P m').filled ⊆ interior (subPoly P m).filled := by
  obtain ⟨m, hm, (⟨hd, rfl | rfl⟩ | ⟨-, rfl⟩)⟩ := mem_cut hm'
  · exact ⟨m, hm, interior_mono (splitPair_split (hs m hm) hd).filled_subset⟩
  · exact ⟨m, hm, interior_mono (splitPair_split (hs m hm) hd).symm.filled_subset⟩
  · exact ⟨_, hm, subset_rfl⟩

/-- **The invariant passes through a cut.** -/
theorem Good.cut {σ : ℝ} {pcs : List (List ℕ)} {d : ℕ × ℕ} {E : List (ℕ × ℕ)}
    (h : Good P σ pcs (d :: E)) : Good P σ (cut P pcs d) E where
  simple m' hm' := by
    obtain ⟨m, hm, (⟨hd, rfl | rfl⟩ | ⟨-, rfl⟩)⟩ := mem_cut hm'
    · exact (splitPair_split (h.simple m hm) hd).simple₁
    · exact (splitPair_split (h.simple m hm) hd).simple₂
    · exact h.simple _ hm
  orient m' hm' := by
    obtain ⟨m, hm, (⟨hd, rfl | rfl⟩ | ⟨-, rfl⟩)⟩ := mem_cut hm'
    · rw [orient_splitFst (h.simple m hm) hd]; exact h.orient m hm
    · rw [orient_splitSnd (h.simple m hm) hd]; exact h.orient m hm
    · exact h.orient _ hm
  disj := by
    unfold Final.cut
    rw [List.pairwise_flatMap]
    refine ⟨fun m hm => ?_, ?_⟩
    · split_ifs with hd
      · exact List.pairwise_pair.2 (splitPair_split (h.simple m hm) hd).interior_disjoint
      · exact List.pairwise_singleton _ _
    · refine h.disj.imp_of_mem fun {m₁ m₂} hm₁ hm₂ hdisj => ?_
      intro x hx y hy
      have hx' : x ∈ Final.cut P [m₁] d := by
        unfold Final.cut; rw [List.flatMap_singleton]; exact hx
      have hy' : y ∈ Final.cut P [m₂] d := by
        unfold Final.cut; rw [List.flatMap_singleton]; exact hy
      obtain ⟨m₁', hm₁', hsub₁⟩ := interior_subset_of_mem_cut
        (fun m hm => by rw [List.mem_singleton] at hm; rw [hm]; exact h.simple _ hm₁) hx'
      obtain ⟨m₂', hm₂', hsub₂⟩ := interior_subset_of_mem_cut
        (fun m hm => by rw [List.mem_singleton] at hm; rw [hm]; exact h.simple _ hm₂) hy'
      rw [List.mem_singleton] at hm₁' hm₂'
      subst hm₁' hm₂'
      exact hdisj.mono hsub₁ hsub₂
  diag e he := by
    classical
    obtain ⟨m, hm, hde⟩ := h.diag e (List.mem_cons_of_mem _ he)
    have hmem : ∀ m', m' ∈ (if IsDiag P m d then [splitFst m d, splitSnd m d] else [m]) →
        m' ∈ Final.cut P pcs d := fun m' hm' => by
      unfold Final.cut; exact List.mem_flatMap.2 ⟨m, hm, hm'⟩
    by_cases hd : IsDiag P m d
    · have hnc : NonCross P d e := (List.pairwise_cons.1 h.noncross).1 e he
      rcases Chazelle.Split.isDiag_split_cases (h.simple m hm) hd hde hnc with
        ⟨-, -, h1⟩ | ⟨-, -, -, h2⟩
      · exact ⟨_, hmem _ (by rw [ite_eq_left hd]; exact List.mem_cons_self), h1⟩
      · exact ⟨_, hmem _ (by rw [ite_eq_left hd]; simp), h2⟩
    · exact ⟨m, hmem _ (by rw [ite_eq_right hd]; exact List.mem_singleton_self _), hde⟩
  noncross := (List.pairwise_cons.1 h.noncross).2

/-- The invariant passes through sequential cutting. -/
theorem Good.seqSplit {σ : ℝ} {pcs : List (List ℕ)} {E : List (ℕ × ℕ)} (h : Good P σ pcs E) :
    Good P σ (Final.seqSplit P pcs E) [] := by
  induction E generalizing pcs with
  | nil => exact h
  | cons d E ih => exact ih h.cut

/-- A simple polygon has a nonempty interior. -/
theorem interior_filled_nonempty {Q : Polygon} (hQ : Q.Simple) : (interior Q.filled).Nonempty := by
  have hn := Chazelle.Jordan.simple_three_le hQ
  obtain ⟨δ, hδ⟩ := (Chazelle.Mountain.eventually_offset_orient hQ (i := 0) (by omega)
    (t := 1 / 2) ⟨by norm_num, by norm_num⟩).exists
  exact ⟨_, by rw [Chazelle.Jordan.interior_filled hQ]; exact hδ.1⟩

/-- **Uniqueness of the piece of a diagonal**: in a list of pieces with pairwise disjoint
interiors, a diagonal of the head piece is a diagonal of no other piece. -/
theorem not_isDiag_of_disj {m : List ℕ} {rest : List (List ℕ)} {d : ℕ × ℕ}
    (hs : (subPoly P m).Simple) (hd : IsDiag P m d)
    (hdisj : ∀ m' ∈ rest, Disjoint (interior (subPoly P m).filled) (interior (subPoly P m').filled))
    (hs' : ∀ m' ∈ rest, (subPoly P m').Simple) : ∀ m' ∈ rest, ¬ IsDiag P m' d := by
  intro m' hm' hd'
  have h1 := isDiag_lerp_mem_interior hs hd (ε := 1 / 2) ⟨by norm_num, by norm_num⟩
  have h2 := isDiag_lerp_mem_interior (hs' m' hm') hd' (ε := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [← Chazelle.Jordan.interior_filled hs] at h1
  rw [← Chazelle.Jordan.interior_filled (hs' m' hm')] at h2
  exact Set.disjoint_left.1 (hdisj m' hm') h1 h2

/-- **The initial invariant**: for an enumeration of the inserted diagonals, the whole polygon
`[List.range P.n]` with orientation `orient P`. -/
theorem good_init (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D) :
    Good P (orient P) [List.range P.n] D where
  simple m hm := by
    rw [List.mem_singleton] at hm; rw [hm, subPoly_range]; exact hP
  orient m hm := by rw [List.mem_singleton] at hm; rw [hm, subPoly_range]
  disj := List.pairwise_singleton _ _
  diag e he := ⟨_, List.mem_singleton_self _, (hD.diagSystem hP).diag e he⟩
  noncross := (hD.diagSystem hP).noncross

/-! ### Index lists -/

section ListFacts

theorem getD_mem_of_lt {c : List ℕ} {t : ℕ} (ht : t < c.length) : c.getD t 0 ∈ c := by
  rw [Chazelle.EarClip.getD_eq_getElem_of_lt _ _ ht]; exact List.getElem_mem ht

theorem getD_inj_of_nodup {c : List ℕ} (hnd : c.Nodup) {t t' : ℕ} (ht : t < c.length)
    (ht' : t' < c.length) (h : c.getD t 0 = c.getD t' 0) : t = t' := by
  rw [Chazelle.EarClip.getD_eq_getElem_of_lt _ _ ht,
    Chazelle.EarClip.getD_eq_getElem_of_lt _ _ ht'] at h
  exact (hnd.getElem_inj_iff).1 h

theorem exists_getD_of_mem {c : List ℕ} {z : ℕ} (h : z ∈ c) : ∃ t < c.length, c.getD t 0 = z := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨t, ht, Chazelle.EarClip.getD_eq_getElem_of_lt _ _ ht⟩

theorem getD_map_of_lt (f : ℕ → ℕ) {c : List ℕ} {t : ℕ} (ht : t < c.length) :
    (c.map f).getD t 0 = f (c.getD t 0) := by
  rw [Chazelle.EarClip.getD_eq_getElem_of_lt _ _ (by rw [List.length_map]; exact ht),
    Chazelle.EarClip.getD_eq_getElem_of_lt _ _ ht, List.getElem_map]

theorem getD_rotate_of_lt {c : List ℕ} (r : ℕ) {t : ℕ} (ht : t < c.length) :
    (c.rotate r).getD t 0 = c.getD ((t + r) % c.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_rotate ht]

theorem getD_take_of_lt {c : List ℕ} {k t : ℕ} (ht : t < k) : (c.take k).getD t 0 = c.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]

theorem getD_drop' (c : List ℕ) (k t : ℕ) : (c.drop k).getD t 0 = c.getD (k + t) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem getD_append_lt {A B : List ℕ} {t : ℕ} (ht : t < A.length) :
    (A ++ B).getD t 0 = A.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

theorem getD_append_ge {A B : List ℕ} {t : ℕ} (ht : A.length ≤ t) :
    (A ++ B).getD t 0 = B.getD (t - A.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right ht]

/-- The last member of `l` satisfying `p` (or `r` if there is none): a left fold. -/
def selectLast (p : ℕ → Bool) (l : List ℕ) (r : ℕ) : ℕ :=
  l.foldl (fun r z => if p z then z else r) r

theorem selectLast_nil (p : ℕ → Bool) (r : ℕ) : selectLast p [] r = r := rfl

theorem selectLast_cons (p : ℕ → Bool) (z : ℕ) (l : List ℕ) (r : ℕ) :
    selectLast p (z :: l) r = selectLast p l (if p z then z else r) := rfl

theorem selectLast_append (p : ℕ → Bool) (l l' : List ℕ) (r : ℕ) :
    selectLast p (l ++ l') r = selectLast p l' (selectLast p l r) := by
  unfold selectLast; rw [List.foldl_append]

/-- If every member satisfying `p` is `x`, selecting from `x` gives `x`. -/
theorem selectLast_self {p : ℕ → Bool} {x : ℕ} :
    ∀ {l : List ℕ}, (∀ z ∈ l, p z = true → z = x) → selectLast p l x = x
  | [], _ => rfl
  | z :: l, h => by
    rw [selectLast_cons]
    by_cases hz : p z = true
    · rw [ite_eq_left hz, h z List.mem_cons_self hz]
      exact selectLast_self fun z' hz' => h z' (List.mem_cons_of_mem _ hz')
    · rw [ite_eq_right hz]
      exact selectLast_self fun z' hz' => h z' (List.mem_cons_of_mem _ hz')

/-- **Selection of the unique passing member**: if `x ∈ l` is the only member satisfying `p`,
the selection returns it, from any start. -/
theorem selectLast_eq_of_unique {l : List ℕ} {p : ℕ → Bool} {x : ℕ} (hx : x ∈ l)
    (hpx : p x = true) (huniq : ∀ z ∈ l, p z = true → z = x) (r : ℕ) : selectLast p l r = x := by
  induction l generalizing r with
  | nil => exact absurd hx List.not_mem_nil
  | cons a l ih =>
    rw [selectLast_cons]
    by_cases ha : p a = true
    · rw [ite_eq_left ha, huniq a List.mem_cons_self ha]
      exact selectLast_self fun z hz => huniq z (List.mem_cons_of_mem _ hz)
    · rw [ite_eq_right ha]
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd hpx ha
      · exact ih hx' (fun z hz hpz => huniq z (List.mem_cons_of_mem _ hz) hpz) _

end ListFacts

/-! ### The linked structure -/

/-- **The linked structure of the pieces.**  Nodes `0 … cnt - 1`; node `z` is a copy of the
vertex `vtx z`, with neighbours `nxt z`, `prv z` in its cycle; `cop v` lists the copies of the
vertex `v`. -/
structure LState where
  vtx : ℕ → ℕ
  nxt : ℕ → ℕ
  prv : ℕ → ℕ
  cnt : ℕ
  cop : ℕ → List ℕ

/-- The initial structure of an `n`-gon: node `i` is vertex `i`, one cycle `0 → 1 → ⋯ → n-1`. -/
def initState (n : ℕ) : LState where
  vtx z := z
  nxt z := (z + 1) % n
  prv z := (z + n - 1) % n
  cnt := n
  cop v := if v < n then [v] else []

/-- **The wedge test at a node**: the vertex `w` passes the `σ`-side wedge test at the corner
`vtx (prv z) → vtx z → vtx (nxt z)` of node `z`. -/
def nodeWedge (P : Polygon) (σ : ℝ) (S : LState) (z w : ℕ) : Prop :=
  wedgeTest σ (P.vtx (S.vtx (S.prv z))) (P.vtx (S.vtx z)) (P.vtx (S.vtx (S.nxt z))) (P.vtx w)

open Classical in
/-- The (last) copy of the vertex `v` whose corner passes the wedge test towards `w` (or `0`);
the copies are scanned in the order of `cop v`. -/
noncomputable def findCopy (P : Polygon) (σ : ℝ) (S : LState) (v w : ℕ) : ℕ :=
  selectLast (fun z => decide (nodeWedge P σ S z w)) (S.cop v) 0

/-- **The surgery** splitting the cycle through the nodes `x` (a copy of `a`) and `y` (a copy of
`b`) into `x → ⋯ → y → x` and `y' → nxt y → ⋯ → prv x → x' → y'`, with the new nodes
`x' = cnt` (a copy of `a`) and `y' = cnt + 1` (a copy of `b`). -/
def surgery (S : LState) (a b x y : ℕ) : LState where
  vtx := upd (upd S.vtx S.cnt a) (S.cnt + 1) b
  nxt := upd (upd (upd (upd S.nxt y x) (S.cnt + 1) (S.nxt y)) (S.prv x) S.cnt) S.cnt (S.cnt + 1)
  prv := upd (upd (upd (upd S.prv x y) (S.nxt y) (S.cnt + 1)) S.cnt (S.prv x)) (S.cnt + 1) S.cnt
  cnt := S.cnt + 2
  cop := upd (upd S.cop a (S.cnt :: S.cop a)) b ((S.cnt + 1) :: S.cop b)

/-- **One step**: split along the diagonal `(a, b)` at the copies chosen by the wedge test. -/
noncomputable def step (P : Polygon) (σ : ℝ) (S : LState) (d : ℕ × ℕ) : LState :=
  surgery S d.1 d.2 (findCopy P σ S d.1 d.2) (findCopy P σ S d.2 d.1)

/-- **The whole run**: process the diagonals in order. -/
noncomputable def runState (P : Polygon) (σ : ℝ) : LState → List (ℕ × ℕ) → LState
  | S, [] => S
  | S, d :: D => runState P σ (step P σ S d) D

/-! ### Cycles -/

/-- `c` is a cycle of the structure: nonempty, and consecutive entries (cyclically) are linked by
`nxt` and `prv`. -/
def IsCyc (S : LState) (c : List ℕ) : Prop :=
  c ≠ [] ∧ ∀ i < c.length, S.nxt (c.getD i 0) = c.getD ((i + 1) % c.length) 0 ∧
    S.prv (c.getD ((i + 1) % c.length) 0) = c.getD i 0

/-- The chain description of a cycle. -/
theorem isCyc_of_chain {S : LState} {c : List ℕ} (hne : c ≠ [])
    (hch : ∀ t, t + 1 < c.length → S.nxt (c.getD t 0) = c.getD (t + 1) 0 ∧
      S.prv (c.getD (t + 1) 0) = c.getD t 0)
    (hn : S.nxt (c.getD (c.length - 1) 0) = c.getD 0 0)
    (hp : S.prv (c.getD 0 0) = c.getD (c.length - 1) 0) : IsCyc S c := by
  refine ⟨hne, fun i hi => ?_⟩
  by_cases h : i + 1 < c.length
  · rw [Nat.mod_eq_of_lt h]; exact hch i h
  · have hi' : i = c.length - 1 := by omega
    have e : (i + 1) % c.length = 0 := by
      rw [show i + 1 = c.length by omega, Nat.mod_self]
    rw [e, hi']; exact ⟨hn, hp⟩

/-- The chain relations of a cycle. -/
theorem IsCyc.chain {S : LState} {c : List ℕ} (h : IsCyc S c) {t : ℕ} (ht : t + 1 < c.length) :
    S.nxt (c.getD t 0) = c.getD (t + 1) 0 ∧ S.prv (c.getD (t + 1) 0) = c.getD t 0 := by
  have := h.2 t (by omega)
  rwa [Nat.mod_eq_of_lt ht] at this

/-- The predecessor in a cycle. -/
theorem IsCyc.prv_getD {S : LState} {c : List ℕ} (h : IsCyc S c) {i : ℕ} (hi : i < c.length) :
    S.prv (c.getD i 0) = c.getD ((i + c.length - 1) % c.length) 0 := by
  have hl : 0 < c.length := by omega
  have := (h.2 ((i + c.length - 1) % c.length) (Nat.mod_lt _ hl)).2
  have e : ((i + c.length - 1) % c.length + 1) % c.length = i := by
    rw [Nat.mod_add_mod, show i + c.length - 1 + 1 = i + c.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  rwa [e] at this

/-- Rotating a cycle gives a cycle. -/
theorem IsCyc.rotate {S : LState} {c : List ℕ} (h : IsCyc S c) (r : ℕ) : IsCyc S (c.rotate r) := by
  have hl : 0 < c.length := List.length_pos_iff.2 h.1
  refine ⟨fun h' => h.1 (List.rotate_eq_nil_iff.1 h'), fun i hi => ?_⟩
  rw [List.length_rotate] at hi ⊢
  rw [getD_rotate_of_lt r hi, getD_rotate_of_lt r (Nat.mod_lt _ hl)]
  have e : ((i + 1) % c.length + r) % c.length = ((i + r) % c.length + 1) % c.length := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod, show i + 1 + r = i + r + 1 by omega]
  rw [e]
  exact h.2 _ (Nat.mod_lt _ hl)

/-- **The representation invariant**: the node lists `cs` partition the nodes `0 … cnt - 1`
into cycles of `S`, and `cop v` lists (without repetition) the copies of `v`. -/
structure Repr (S : LState) (cs : List (List ℕ)) : Prop where
  nodup : cs.flatten.Nodup
  mem : ∀ z, z ∈ cs.flatten ↔ z < S.cnt
  cyc : ∀ c ∈ cs, IsCyc S c
  cop : ∀ v z, z ∈ S.cop v ↔ z < S.cnt ∧ S.vtx z = v
  copNodup : ∀ v, (S.cop v).Nodup

theorem Repr.perm {S : LState} {cs cs' : List (List ℕ)} (h : Repr S cs) (hp : List.Perm cs cs') :
    Repr S cs' where
  nodup := hp.flatten.nodup_iff.1 h.nodup
  mem z := by rw [← hp.flatten.mem_iff]; exact h.mem z
  cyc c hc := h.cyc c (hp.mem_iff.2 hc)
  cop := h.cop
  copNodup := h.copNodup

/-- Replacing the head cycle by a rotation keeps the representation. -/
theorem Repr.rotate_head {S : LState} {c : List ℕ} {rest : List (List ℕ)} (h : Repr S (c :: rest))
    (r : ℕ) : Repr S (c.rotate r :: rest) where
  nodup := by
    have h1 := h.nodup
    rw [List.flatten_cons] at h1 ⊢
    exact ((List.rotate_perm c r).append_right _).nodup_iff.2 h1
  mem z := by
    rw [← h.mem z, List.flatten_cons, List.flatten_cons, List.mem_append, List.mem_append,
      List.mem_rotate]
  cyc c' hc' := by
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact (h.cyc c List.mem_cons_self).rotate r
    · exact h.cyc c' (List.mem_cons_of_mem _ hc')
  cop := h.cop
  copNodup := h.copNodup

/-- **The wedge test at a node of a cycle is the wedge test of the piece.**  For a cycle `c` and
a position `i`, the node wedge test at `c[i]` is the wedge test at vertex `i` of the sub-polygon
of the vertex list `c.map vtx`. -/
theorem nodeWedge_iff {S : LState} {c : List ℕ} (hc : IsCyc S c) {i : ℕ} (hi : i < c.length)
    (σ : ℝ) (w : ℕ) :
    nodeWedge P σ S (c.getD i 0) w ↔
      wedgeTest σ ((subPoly P (c.map S.vtx)).vtx (Chazelle.Jordan.prevIdx (subPoly P (c.map S.vtx)) i))
        ((subPoly P (c.map S.vtx)).vtx i)
        ((subPoly P (c.map S.vtx)).vtx ((i + 1) % (subPoly P (c.map S.vtx)).n)) (P.vtx w) := by
  have hl : 0 < c.length := by omega
  have hn : (subPoly P (c.map S.vtx)).n = c.length := by rw [n_subPoly, List.length_map]
  have hv : ∀ j < c.length, (subPoly P (c.map S.vtx)).vtx j = P.vtx (S.vtx (c.getD j 0)) := by
    intro j hj
    rw [Chazelle.EarClip.vtx_subPoly_getD P _ (by rw [List.length_map]; exact hj),
      getD_map_of_lt _ hj]
  unfold nodeWedge Chazelle.Jordan.prevIdx
  rw [hn, hv _ (Nat.mod_lt _ hl), hv _ hi, hv _ (Nat.mod_lt _ hl), (hc.2 i hi).1,
    hc.prv_getD hi]

/-! ### The surgery -/

section Surgery

variable {S : LState} {a b x y : ℕ}

theorem surgery_vtx_old {z : ℕ} (hz : z < S.cnt) : (surgery S a b x y).vtx z = S.vtx z := by
  simp only [surgery, upd]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem surgery_vtx_x' : (surgery S a b x y).vtx S.cnt = a := by
  simp only [surgery, upd]; simp

theorem surgery_vtx_y' : (surgery S a b x y).vtx (S.cnt + 1) = b := by
  simp only [surgery, upd]; simp

/-- **Correctness of the surgery.**  Let `c` be a cycle of a represented structure, with the
copy `x = c[0]` of `a` and the copy `y = c[L]` of `b ≠ a`, `2 ≤ L ≤ c.length - 2`.  After the
surgery the structure represents the cycles `c[0 … L]` and `y', c[L+1 …], x'` together with the
other cycles. -/
theorem surgery_spec {c : List ℕ} {rest : List (List ℕ)} (hR : Repr S (c :: rest)) {L : ℕ}
    (hL2 : 2 ≤ L) (hLn : L + 2 ≤ c.length) (hab : a ≠ b) (hva : S.vtx (c.getD 0 0) = a)
    (hvb : S.vtx (c.getD L 0) = b) :
    Repr (surgery S a b (c.getD 0 0) (c.getD L 0))
      (c.take (L + 1) :: ((S.cnt + 1) :: (c.drop (L + 1) ++ [S.cnt])) :: rest) := by
  set N := S.cnt with hN
  set len := c.length with hlen
  set x := c.getD 0 0 with hx
  set y := c.getD L 0 with hy
  set S' := surgery S a b x y with hS'
  have hflat := hR.nodup
  rw [List.flatten_cons, List.nodup_append] at hflat
  obtain ⟨hnd, hrnd, hdisj⟩ := hflat
  have hltc : ∀ z ∈ c, z < N := fun z hz =>
    (hR.mem z).1 (by rw [List.flatten_cons]; exact List.mem_append_left _ hz)
  have hltr : ∀ z ∈ rest.flatten, z < N := fun z hz =>
    (hR.mem z).1 (by rw [List.flatten_cons]; exact List.mem_append_right _ hz)
  have hcyc := hR.cyc c List.mem_cons_self
  have hg_lt : ∀ t < len, c.getD t 0 < N := fun t ht => hltc _ (getD_mem_of_lt ht)
  have hg_ne : ∀ t t', t < len → t' < len → t ≠ t' → c.getD t 0 ≠ c.getD t' 0 :=
    fun t t' ht ht' hne h => hne (getD_inj_of_nodup hnd ht ht' h)
  have hpx : S.prv x = c.getD (len - 1) 0 := by
    rw [hx, hcyc.prv_getD (by omega), show 0 + len - 1 = len - 1 by omega,
      Nat.mod_eq_of_lt (by omega)]
  have hny : S.nxt y = c.getD (L + 1) 0 := (hcyc.chain (t := L) (by omega)).1
  -- evaluation of the new links
  have nxt_old : ∀ z, z ≠ y → z ≠ c.getD (len - 1) 0 → z < N → S'.nxt z = S.nxt z := by
    intro z h1 h2 h3
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_right (by rw [hpx]; exact h2), ite_eq_right (by omega), ite_eq_right h1]
  have nxt_y : S'.nxt y = x := by
    have h1 := hg_ne L (len - 1) (by omega) (by omega) (by omega)
    have h2 := hg_lt L (by omega)
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_right (by rw [hpx]; exact h1), ite_eq_right (by omega)]; simp
  have nxt_px : S'.nxt (c.getD (len - 1) 0) = N := by
    have h2 := hg_lt (len - 1) (by omega)
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_left hpx.symm]
  have nxt_N : S'.nxt N = N + 1 := by
    simp only [hS', surgery, upd]; simp [hN]
  have nxt_N1 : S'.nxt (N + 1) = c.getD (L + 1) 0 := by
    have h2 := hg_lt (len - 1) (by omega)
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_right (by rw [hpx]; omega), ite_eq_left rfl, hny]
  have prv_old : ∀ z, z ≠ x → z ≠ c.getD (L + 1) 0 → z < N → S'.prv z = S.prv z := by
    intro z h1 h2 h3
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [hny]; exact h2), ite_eq_right h1]
  have prv_x : S'.prv x = y := by
    have h1 := hg_ne 0 (L + 1) (by omega) (by omega) (by omega)
    have h2 := hg_lt 0 (by omega)
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [hny]; exact h1)]; simp
  have prv_ny : S'.prv (c.getD (L + 1) 0) = N + 1 := by
    have h2 := hg_lt (L + 1) (by omega)
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hny.symm]
  have prv_N : S'.prv N = c.getD (len - 1) 0 := by
    simp only [hS', surgery, upd]
    rw [ite_eq_right (by omega), ite_eq_left rfl, hpx]
  have prv_N1 : S'.prv (N + 1) = N := by
    simp only [hS', surgery, upd]; simp [hN]
  -- the first new cycle
  have hlen1 : (c.take (L + 1)).length = L + 1 := by rw [List.length_take]; omega
  have hcyc1 : IsCyc S' (c.take (L + 1)) := by
    refine isCyc_of_chain (by rw [← List.length_pos_iff, hlen1]; omega) ?_ ?_ ?_
    · intro t ht
      rw [hlen1] at ht
      rw [getD_take_of_lt (by omega), getD_take_of_lt (by omega)]
      have hc := hcyc.chain (t := t) (by omega)
      refine ⟨?_, ?_⟩
      · rw [nxt_old _ (hg_ne t L (by omega) (by omega) (by omega))
          (hg_ne t (len - 1) (by omega) (by omega) (by omega)) (hg_lt t (by omega))]
        exact hc.1
      · rw [prv_old _ (hg_ne (t + 1) 0 (by omega) (by omega) (by omega))
          (hg_ne (t + 1) (L + 1) (by omega) (by omega) (by omega)) (hg_lt (t + 1) (by omega))]
        exact hc.2
    · rw [hlen1, show L + 1 - 1 = L by omega, getD_take_of_lt (by omega),
        getD_take_of_lt (by omega)]
      exact nxt_y
    · rw [hlen1, show L + 1 - 1 = L by omega, getD_take_of_lt (by omega),
        getD_take_of_lt (by omega)]
      exact prv_x
  -- the second new cycle
  set c2 := (N + 1) :: (c.drop (L + 1) ++ [N]) with hc2
  have hlenA : (c.drop (L + 1)).length = len - L - 1 := by rw [List.length_drop]; omega
  have hlen2 : c2.length = len - L + 1 := by
    rw [hc2, List.length_cons, List.length_append, hlenA, List.length_singleton]; omega
  have hg2_0 : c2.getD 0 0 = N + 1 := rfl
  have hg2_mid : ∀ u, u < len - L - 1 → c2.getD (u + 1) 0 = c.getD (L + 1 + u) 0 := by
    intro u hu
    rw [hc2, List.getD_cons_succ, getD_append_lt (by rw [hlenA]; exact hu), getD_drop']
  have hg2_last : c2.getD (len - L) 0 = N := by
    rw [hc2, show len - L = (len - L - 1) + 1 by omega, List.getD_cons_succ,
      getD_append_ge (by rw [hlenA]), hlenA, Nat.sub_self]
    rfl
  have hcyc2 : IsCyc S' c2 := by
    refine isCyc_of_chain (by rw [hc2]; exact List.cons_ne_nil _ _) ?_ ?_ ?_
    · intro t ht
      rw [hlen2] at ht
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · rw [hg2_0, show 0 + 1 = 0 + 1 from rfl, hg2_mid 0 (by omega), Nat.add_zero]
        exact ⟨nxt_N1, prv_ny⟩
      · obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
        rw [hg2_mid u (by omega)]
        by_cases hu : u + 1 < len - L - 1
        · rw [hg2_mid (u + 1) hu]
          have hc := hcyc.chain (t := L + 1 + u) (by omega)
          rw [show L + 1 + (u + 1) = L + 1 + u + 1 by omega]
          refine ⟨?_, ?_⟩
          · rw [nxt_old _ (hg_ne _ L (by omega) (by omega) (by omega))
              (hg_ne _ (len - 1) (by omega) (by omega) (by omega)) (hg_lt _ (by omega))]
            exact hc.1
          · rw [prv_old _ (hg_ne _ 0 (by omega) (by omega) (by omega))
              (hg_ne _ (L + 1) (by omega) (by omega) (by omega)) (hg_lt _ (by omega))]
            exact hc.2
        · have hu' : u + 1 = len - L - 1 := by omega
          rw [show u + 1 + 1 = len - L by omega, hg2_last,
            show L + 1 + u = len - 1 by omega]
          exact ⟨nxt_px, prv_N⟩
    · rw [hlen2, show len - L + 1 - 1 = len - L by omega, hg2_last, hg2_0]
      exact nxt_N
    · rw [hlen2, show len - L + 1 - 1 = len - L by omega, hg2_last, hg2_0]
      exact prv_N1
  -- the other cycles are untouched
  have hcycr : ∀ c'' ∈ rest, IsCyc S' c'' := by
    intro c'' hc''
    have hold := hR.cyc c'' (List.mem_cons_of_mem _ hc'')
    have hin : ∀ z ∈ c'', z ∈ rest.flatten := fun z hz => List.mem_flatten.2 ⟨c'', hc'', hz⟩
    have hnotc : ∀ z ∈ c'', z ∉ c := fun z hz hzc => hdisj z hzc z (hin z hz) rfl
    refine ⟨hold.1, fun i hi => ?_⟩
    have hl : 0 < c''.length := by omega
    have hz1 := getD_mem_of_lt hi
    have hz2 := getD_mem_of_lt (Nat.mod_lt (i + 1) hl)
    rw [nxt_old _ (fun h => hnotc _ hz1 (by rw [h]; exact getD_mem_of_lt (by omega)))
      (fun h => hnotc _ hz1 (by rw [h]; exact getD_mem_of_lt (by omega))) (hltr _ (hin _ hz1)),
      prv_old _ (fun h => hnotc _ hz2 (by rw [h]; exact getD_mem_of_lt (by omega)))
      (fun h => hnotc _ hz2 (by rw [h]; exact getD_mem_of_lt (by omega))) (hltr _ (hin _ hz2))]
    exact hold.2 i hi
  -- the flattening
  have hperm : List.Perm (c.take (L + 1) :: c2 :: rest).flatten
      (c ++ rest.flatten ++ [N + 1, N]) := by
    rw [List.flatten_cons, List.flatten_cons, hc2]
    conv_rhs => rw [← List.take_append_drop (L + 1) c]
    rw [List.perm_iff_count]
    intro v
    simp only [List.count_append, List.count_cons, List.count_nil, List.cons_append]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [← List.flatten_cons]; exact hR.nodup
    · intro z hz w hw
      have : z < N := (hR.mem z).1 (by rw [List.flatten_cons]; exact hz)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      omega
  · intro z
    rw [hperm.mem_iff, List.mem_append, ← List.flatten_cons, hR.mem z]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    show _ ↔ z < N + 2
    omega
  · intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hcyc1
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact hcyc2
    · exact hcycr c' hc'
  · intro v z
    have hcop := hR.cop
    have hnc : ∀ w u, N ≤ u → u ∉ S.cop w := fun w u hu h => by
      have := ((hcop w u).1 h).1; omega
    show z ∈ upd (upd S.cop a (N :: S.cop a)) b ((N + 1) :: S.cop b) v ↔
      z < N + 2 ∧ upd (upd S.vtx N a) (N + 1) b z = v
    have hvz : upd (upd S.vtx N a) (N + 1) b z =
        if z = N + 1 then b else if z = N then a else S.vtx z := rfl
    have hcz : upd (upd S.cop a (N :: S.cop a)) b ((N + 1) :: S.cop b) v =
        if v = b then (N + 1) :: S.cop b else if v = a then N :: S.cop a else S.cop v := rfl
    rw [hvz, hcz]
    rcases lt_trichotomy z N with hz | hz | hz
    · rw [ite_eq_right (show ¬ z = N + 1 by omega), ite_eq_right (show ¬ z = N by omega)]
      split_ifs with h1 h2
      · subst h1
        rw [List.mem_cons, hcop]
        constructor
        · rintro (h | h)
          · omega
          · exact ⟨by omega, h.2⟩
        · rintro ⟨-, h⟩; exact Or.inr ⟨hz, h⟩
      · subst h2
        rw [List.mem_cons, hcop]
        constructor
        · rintro (h | h)
          · omega
          · exact ⟨by omega, h.2⟩
        · rintro ⟨-, h⟩; exact Or.inr ⟨hz, h⟩
      · rw [hcop]
        constructor
        · rintro ⟨-, h⟩; exact ⟨by omega, h⟩
        · rintro ⟨-, h⟩; exact ⟨hz, h⟩
    · subst hz
      rw [ite_eq_right (show ¬ N = N + 1 by omega), ite_eq_left rfl]
      split_ifs with h1 h2
      · subst h1
        simp only [List.mem_cons, hnc _ _ le_rfl, or_false]
        constructor
        · intro h; omega
        · rintro ⟨-, h⟩; exact absurd h hab
      · subst h2; simp
      · simp only [hnc _ _ le_rfl, false_iff, not_and]
        intro _ h; exact h2 h.symm
    · by_cases hz1 : z = N + 1
      · subst hz1
        rw [ite_eq_left rfl]
        split_ifs with h1 h2
        · subst h1; simp
        · subst h2
          simp only [List.mem_cons, hnc _ _ (by omega : N ≤ N + 1), or_false]
          constructor
          · intro h; omega
          · rintro ⟨-, h⟩; exact absurd h.symm hab
        · simp only [hnc _ _ (by omega : N ≤ N + 1), false_iff, not_and]
          intro _ h; exact h1 h.symm
      · rw [ite_eq_right hz1, ite_eq_right (show ¬ z = N by omega)]
        have hzN : ¬ z < N + 2 := by omega
        simp only [hzN, false_and, iff_false]
        split_ifs with h1 h2
        · simp only [List.mem_cons, hnc _ _ hz.le, or_false]; omega
        · simp only [List.mem_cons, hnc _ _ hz.le, or_false]; omega
        · exact hnc _ _ hz.le
  · intro v
    show (upd (upd S.cop a (N :: S.cop a)) b ((N + 1) :: S.cop b) v).Nodup
    have hnc : ∀ w, N ∉ S.cop w ∧ N + 1 ∉ S.cop w := fun w =>
      ⟨fun h => by have := ((hR.cop w N).1 h).1; omega,
       fun h => by have := ((hR.cop w (N + 1)).1 h).1; omega⟩
    simp only [upd]
    split_ifs with h1 h2
    · exact List.nodup_cons.2 ⟨(hnc b).2, hR.copNodup b⟩
    · exact List.nodup_cons.2 ⟨(hnc a).1, hR.copNodup a⟩
    · exact hR.copNodup v

end Surgery

/-! ### One step -/

section Step

open Chazelle.Split (diagLen diagLen_spec getD_idxOf isDiagonal_of_isDiag nodup_of_simple arcList)

/-- The second piece of a split, as the part of the rotation to `d.1` after `d.2`, closed by
`d.1`: `splitSnd m d = d.2 :: (m.rotate i).drop (L + 1) ++ [d.1]` with `i` the position of `d.1`
and `L = diagLen m d`. -/
theorem splitSnd_eq_cons {m : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ m) (h2 : d.2 ∈ m) (hne : d.1 ≠ d.2) :
    splitSnd m d = d.2 :: ((m.rotate (m.idxOf d.1)).drop (diagLen m d + 1) ++ [d.1]) := by
  obtain ⟨hL1, hLn, hsL⟩ := diagLen_spec h1 h2 hne
  set i := m.idxOf d.1 with hi
  set L := diagLen m d with hL
  have hlen : (m.rotate i).length = m.length := List.length_rotate _ _
  have e1 : m.rotate (m.idxOf d.2) = (m.rotate i).rotate L := by
    rw [List.rotate_rotate, ← List.rotate_mod m (i + L), hsL]
  unfold splitSnd arcList
  rw [e1, List.rotate_eq_drop_append_take (by omega), List.take_append,
    List.take_of_length_le (by rw [List.length_drop]; omega), List.length_drop, hlen,
    show m.length - L + 1 - (m.length - L) = 1 by omega, List.take_take,
    show min 1 L = 1 by omega, List.drop_eq_getElem_cons (by omega), List.take_one]
  have hM0 : (m.rotate i).head? = some d.1 := by
    rw [List.head?_eq_getElem?, List.getElem?_rotate (by omega), Nat.zero_add,
      Nat.mod_eq_of_lt (List.idxOf_lt_length_of_mem h1), List.getElem?_eq_getElem
      (List.idxOf_lt_length_of_mem h1), List.getElem_idxOf]
  have hML : (m.rotate i)[L]'(by omega) = d.2 := by
    rw [List.getElem_rotate]
    have : (L + i) % m.length = m.idxOf d.2 := by rw [Nat.add_comm]; exact hsL
    simp only [this, List.getElem_idxOf]
  rw [hM0, hML]
  rfl

variable {σ : ℝ} {S : LState} {c : List ℕ} {rest : List (List ℕ)}

/-- **The wedge test finds the right copy.**  Let `c :: rest` be the cycles of a represented
structure whose vertex lists satisfy the invariant, `e` an interior diagonal of the head piece
`c.map vtx`, and `c[t₀]` the node of `e.1` in `c`.  Then the first copy of `e.1` passing the wedge
test towards `e.2` is `c[t₀]`: it passes (`wedge_of_isDiag`), and a copy in another cycle fails
(its piece has an interior disjoint from the head piece, `not_wedge_of_disjoint`). -/
theorem findCopy_eq {E : List (ℕ × ℕ)} (hR : Repr S (c :: rest))
    (hG : Good P σ ((c :: rest).map (List.map S.vtx)) E) {e : ℕ × ℕ}
    (he : IsDiag P (c.map S.vtx) e) {t₀ : ℕ} (ht₀ : t₀ < c.length)
    (hv : S.vtx (c.getD t₀ 0) = e.1) : findCopy P σ S e.1 e.2 = c.getD t₀ 0 := by
  classical
  set m := c.map S.vtx with hm
  have hmem : m ∈ (c :: rest).map (List.map S.vtx) := List.mem_map_of_mem List.mem_cons_self
  have hs : (subPoly P m).Simple := hG.simple m hmem
  have hor : orient (subPoly P m) = σ := hG.orient m hmem
  have hmnd : m.Nodup := nodup_of_simple P hs
  have hdisj := hG.disj
  rw [List.map_cons, List.pairwise_cons] at hdisj
  have hcyc := hR.cyc c List.mem_cons_self
  have hlt : ∀ z, z ∈ c ++ rest.flatten ↔ z < S.cnt := by
    intro z; rw [← List.flatten_cons]; exact hR.mem z
  unfold findCopy
  refine selectLast_eq_of_unique ?_ ?_ ?_ 0
  · exact (hR.cop _ _).2 ⟨(hlt _).1 (List.mem_append_left _ (getD_mem_of_lt ht₀)), hv⟩
  · rw [decide_eq_true_iff, nodeWedge_iff hcyc ht₀, ← hor]
    exact wedge_of_isDiag hs he (by rw [List.length_map]; exact ht₀)
      (by rw [getD_map_of_lt _ ht₀, hv])
  · intro z hz hpz
    rw [decide_eq_true_iff] at hpz
    obtain ⟨hzlt, hzv⟩ := (hR.cop _ _).1 hz
    rcases List.mem_append.1 ((hlt z).2 hzlt) with hzc | hzr
    · obtain ⟨t, ht, rfl⟩ := exists_getD_of_mem hzc
      have hmt : m.getD t 0 = m.getD t₀ 0 := by
        rw [getD_map_of_lt _ ht, getD_map_of_lt _ ht₀, hzv, hv]
      rw [getD_inj_of_nodup hmnd (by rw [List.length_map]; exact ht)
        (by rw [List.length_map]; exact ht₀) hmt]
    · exfalso
      obtain ⟨c'', hc'', hzc''⟩ := List.mem_flatten.1 hzr
      obtain ⟨t, ht, rfl⟩ := exists_getD_of_mem hzc''
      have hcyc'' := hR.cyc c'' (List.mem_cons_of_mem _ hc'')
      have hmem'' : c''.map S.vtx ∈ (c :: rest).map (List.map S.vtx) :=
        List.mem_map_of_mem (List.mem_cons_of_mem _ hc'')
      have hs'' := hG.simple _ hmem''
      rw [nodeWedge_iff hcyc'' ht, ← hG.orient _ hmem''] at hpz
      have hvt : (subPoly P (c''.map S.vtx)).vtx t = P.vtx e.1 := by
        rw [Chazelle.EarClip.vtx_subPoly_getD P _ (by rw [List.length_map]; exact ht),
          getD_map_of_lt _ ht, hzv]
      refine not_wedge_of_disjoint hs'' (by rw [n_subPoly, List.length_map]; exact ht)
        (U := (subPoly P m).filled \ (subPoly P m).boundary) ?_ ?_ hpz
      · intro ε hε
        rw [hvt]
        exact isDiag_lerp_mem_interior hs he hε
      · rw [← Chazelle.Jordan.interior_filled hs, ← Chazelle.Jordan.interior_filled hs'']
        exact hdisj.1 _ (List.mem_map_of_mem hc'')

/-- **One step on the head cycle.**  If the head piece `c.map vtx` has `d` as an interior
diagonal, processing `d` gives a represented structure whose vertex lists are exactly the cut
of the vertex lists. -/
theorem step_spec_head {d : ℕ × ℕ} {E : List (ℕ × ℕ)} (hR : Repr S (c :: rest))
    (hG : Good P σ ((c :: rest).map (List.map S.vtx)) (d :: E)) (hd : IsDiag P (c.map S.vtx) d) :
    ∃ cs', Repr (step P σ S d) cs' ∧
      cs'.map (List.map (step P σ S d).vtx) = cut P ((c :: rest).map (List.map S.vtx)) d := by
  set m := c.map S.vtx with hm
  have hmem : m ∈ (c :: rest).map (List.map S.vtx) := List.mem_map_of_mem List.mem_cons_self
  have hs : (subPoly P m).Simple := hG.simple m hmem
  have hmnd : m.Nodup := nodup_of_simple P hs
  have hlenm : m.length = c.length := List.length_map _
  have hdisj := hG.disj
  rw [List.map_cons, List.pairwise_cons] at hdisj
  have hnot : ∀ m' ∈ rest.map (List.map S.vtx), ¬ IsDiag P m' d :=
    not_isDiag_of_disj hs hd hdisj.1 fun m' hm' =>
      hG.simple m' (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hm')
  obtain ⟨hL1, hLn, hsL⟩ := diagLen_spec hd.1 hd.2.1 hd.2.2.1
  set i := m.idxOf d.1 with hi_def
  set j := m.idxOf d.2 with hj_def
  set L := diagLen m d with hL_def
  have hi : i < m.length := List.idxOf_lt_length_of_mem hd.1
  have hj : j < m.length := List.idxOf_lt_length_of_mem hd.2.1
  have hmi : m.getD i 0 = d.1 := getD_idxOf hd.1
  have hmj : m.getD j 0 = d.2 := getD_idxOf hd.2.1
  have hdiag := isDiagonal_of_isDiag hs hd hi hmi hL1 hLn (by rw [hsL]; exact hmj)
  have hL2 : 2 ≤ L := hdiag.1
  have hL2' : L + 2 ≤ m.length := by have := hdiag.2.1; rwa [n_subPoly] at this
  have hi' : i < c.length := by omega
  have hj' : j < c.length := by omega
  have hvx : S.vtx (c.getD i 0) = d.1 := by rw [← getD_map_of_lt S.vtx hi', ← hm, hmi]
  have hvy : S.vtx (c.getD j 0) = d.2 := by rw [← getD_map_of_lt S.vtx hj', ← hm, hmj]
  have hfx : findCopy P σ S d.1 d.2 = c.getD i 0 := findCopy_eq hR hG hd hi' hvx
  have hfy : findCopy P σ S d.2 d.1 = c.getD j 0 :=
    findCopy_eq (e := d.swap) hR hG (Chazelle.Split.IsDiag.swap hd) hj' hvy
  have hstep : step P σ S d = surgery S d.1 d.2 (c.getD i 0) (c.getD j 0) := by
    unfold step; rw [hfx, hfy]
  set c' := c.rotate i with hc'
  have hlenc' : c'.length = c.length := List.length_rotate _ _
  have hc'0 : c'.getD 0 0 = c.getD i 0 := by
    rw [getD_rotate_of_lt i (by omega), Nat.zero_add, Nat.mod_eq_of_lt hi']
  have hc'L : c'.getD L 0 = c.getD j 0 := by
    rw [getD_rotate_of_lt i (by omega), Nat.add_comm, ← hlenm, hsL]
  have hsur := surgery_spec (hR.rotate_head i) hL2 (by rw [List.length_rotate]; omega) hd.2.2.1
    (by rw [← hc', hc'0]; exact hvx) (by rw [← hc', hc'L]; exact hvy)
  rw [← hc', hc'0, hc'L, ← hstep] at hsur
  refine ⟨_, hsur, ?_⟩
  have hvold : ∀ l : List ℕ, (∀ z ∈ l, z < S.cnt) →
      l.map (step P σ S d).vtx = l.map S.vtx := by
    intro l hl
    apply List.map_congr_left
    intro z hz
    rw [hstep]; exact surgery_vtx_old (hl z hz)
  have hltc : ∀ z ∈ c, z < S.cnt := fun z hz =>
    (hR.mem z).1 (by rw [List.flatten_cons]; exact List.mem_append_left _ hz)
  have hltc' : ∀ z ∈ c', z < S.cnt := fun z hz => hltc z (List.mem_rotate.1 hz)
  show _ = cut P (m :: rest.map (List.map S.vtx)) d
  rw [cut_cons_of_isDiag hd, cut_eq_self hnot, List.map_cons, List.map_cons]
  congr 1
  · rw [hvold _ fun z hz => hltc' z (List.mem_of_mem_take hz), List.map_take, hc',
      List.map_rotate]
    rfl
  congr 1
  · rw [splitSnd_eq_cons hd.1 hd.2.1 hd.2.2.1, List.map_cons, List.map_append, List.map_singleton,
      hstep, surgery_vtx_y', surgery_vtx_x', ← hstep,
      hvold _ fun z hz => hltc' z (List.mem_of_mem_drop hz), List.map_drop, hc', List.map_rotate]
  · apply List.map_congr_left
    intro c'' hc''
    apply hvold
    intro z hz
    exact (hR.mem z).1 (by
      rw [List.flatten_cons]
      exact List.mem_append_right _ (List.mem_flatten.2 ⟨c'', hc'', hz⟩))

/-- **One step.**  If the cycles `cs` of a represented structure read, up to order, as a list of
pieces `pcs` satisfying the invariant for `d :: E`, then after processing `d` the new cycles read,
up to order, as `cut P pcs d`. -/
theorem step_spec {cs pcs : List (List ℕ)} {d : ℕ × ℕ} {E : List (ℕ × ℕ)} (hR : Repr S cs)
    (hp : List.Perm (cs.map (List.map S.vtx)) pcs) (hG : Good P σ pcs (d :: E)) :
    ∃ cs', Repr (step P σ S d) cs' ∧
      List.Perm (cs'.map (List.map (step P σ S d).vtx)) (cut P pcs d) := by
  classical
  obtain ⟨m, hm, hd⟩ := hG.diag d List.mem_cons_self
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (hp.mem_iff.2 hm)
  have hcs : List.Perm cs (c :: cs.erase c) := List.perm_cons_erase hc
  have hp' : List.Perm ((c :: cs.erase c).map (List.map S.vtx)) pcs :=
    (hcs.map _).symm.trans hp
  obtain ⟨cs', h1, h2⟩ := step_spec_head (hR.perm hcs) (hG.perm hp'.symm) hd
  exact ⟨cs', h1, by rw [h2]; exact cut_perm hp' d⟩

end Step

/-! ### The whole run -/

section Run

variable {σ : ℝ}

@[simp] theorem runState_nil (S : LState) : runState P σ S [] = S := rfl

theorem runState_cons (S : LState) (d : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    runState P σ S (d :: D) = runState P σ (step P σ S d) D := rfl

/-- **The run simulates sequential cutting** (general form). -/
theorem runState_spec_gen (E : List (ℕ × ℕ)) :
    ∀ (S : LState) (cs pcs : List (List ℕ)), Repr S cs →
      List.Perm (cs.map (List.map S.vtx)) pcs → Good P σ pcs E →
      ∃ cs', Repr (runState P σ S E) cs' ∧
        List.Perm (cs'.map (List.map (runState P σ S E).vtx)) (seqSplit P pcs E) := by
  induction E with
  | nil => intro S cs pcs hR hp _; exact ⟨cs, hR, hp⟩
  | cons d E ih =>
    intro S cs pcs hR hp hG
    obtain ⟨cs', hR', hp'⟩ := step_spec hR hp hG
    exact ih _ cs' _ hR' hp' hG.cut

/-- The initial structure represents the single cycle `0 → 1 → ⋯ → n - 1`. -/
theorem repr_init {n : ℕ} (hn : 0 < n) : Repr (initState n) [List.range n] where
  nodup := by rw [List.flatten_singleton]; exact List.nodup_range
  mem z := by rw [List.flatten_singleton, List.mem_range]; rfl
  cyc c hc := by
    rw [List.mem_singleton] at hc
    subst hc
    refine ⟨by rw [← List.length_pos_iff, List.length_range]; exact hn, fun i hi => ?_⟩
    rw [List.length_range] at hi ⊢
    rw [Chazelle.EarClip.getD_range hi, Chazelle.EarClip.getD_range (Nat.mod_lt _ hn)]
    refine ⟨rfl, ?_⟩
    show ((i + 1) % n + n - 1) % n = i
    by_cases h : i + 1 < n
    · rw [Nat.mod_eq_of_lt h, show i + 1 + n - 1 = i + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
    · rw [show i + 1 = n by omega, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  cop v z := by
    show z ∈ (if v < n then [v] else []) ↔ z < n ∧ z = v
    split_ifs with h
    · rw [List.mem_singleton]; constructor
      · rintro rfl; exact ⟨h, rfl⟩
      · rintro ⟨-, rfl⟩; rfl
    · simp only [List.not_mem_nil, false_iff, not_and]
      rintro hz rfl; exact h hz
  copNodup v := by
    show (if v < n then [v] else []).Nodup
    split_ifs
    · exact List.nodup_singleton _
    · exact List.nodup_nil

/-- **Main theorem of the linked splitting.**  For a simple polygon `P` and an enumeration `D`
of its inserted diagonals, the structure obtained by processing `D` from `initState P.n` with
`σ = orient P` represents cycles `cs` whose vertex lists are, up to order, exactly the pieces
`splitAll (List.range P.n) D`. -/
theorem runState_spec (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D) :
    ∃ cs, Repr (runState P (orient P) (initState P.n) D) cs ∧
      List.Perm (cs.map (List.map (runState P (orient P) (initState P.n) D).vtx))
        (splitAll (List.range P.n) D) := by
  have hn : 0 < P.n := by have := Chazelle.Jordan.simple_three_le hP; omega
  have hmap : [List.range P.n].map (List.map (initState P.n).vtx) = [List.range P.n] := by
    simp only [List.map_cons, List.map_nil]
    congr 1
    exact List.map_id' _
  obtain ⟨cs, hR, hp⟩ := runState_spec_gen (σ := orient P) D (initState P.n) _ _ (repr_init hn)
    (by rw [hmap]) (good_init hP hD)
  exact ⟨cs, hR, by rw [← seqSplit_eq_splitAll (hD.diagSystem hP)]; exact hp⟩

end Run

/-! ### Reading the cycles -/

section Read

/-- Walk `k` steps along `nxt` from the node `z`. -/
def walk (S : LState) (z : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => z :: walk S (S.nxt z) k

theorem walk_eq_map {S : LState} {c : List ℕ} (hc : IsCyc S c) (k : ℕ) :
    ∀ i < c.length, walk S (c.getD i 0) k =
      (List.range k).map fun t => c.getD ((i + t) % c.length) 0 := by
  have hl : 0 < c.length := List.length_pos_iff.2 hc.1
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    intro i hi
    rw [walk, (hc.2 i hi).1, ih _ (Nat.mod_lt _ hl), List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    · simp only [Nat.add_zero, Nat.mod_eq_of_lt hi]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp]
    rw [Nat.mod_add_mod, show i + 1 + t = i + (t + 1) by omega]

/-- **Walking a cycle from any of its nodes reads a rotation of it.** -/
theorem walk_eq_rotate {S : LState} {c : List ℕ} (hc : IsCyc S c) {i : ℕ} (hi : i < c.length) :
    walk S (c.getD i 0) c.length = c.rotate i := by
  rw [walk_eq_map hc _ i hi]
  apply List.ext_getElem
  · simp
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem_rotate, ← Chazelle.EarClip.getD_eq_getElem_of_lt _ 0 (Nat.mod_lt _ (by omega)),
      Nat.add_comm]

end Read

/-! ### Rotations of pieces and the triangulation of the cycles -/

section Assemble

open Chazelle.Existence (WeakTriangulates relabel filled_rotate simple_rotate triangulates_of_weak)
open Chazelle.EarClip (relabelList subPoly_rotate weakTriangulates_rotate)
open Chazelle.Mountain (IsPieceEdge)

/-- **Pieces are closed under rotation.** -/
theorem isPiece_rotate {l : List ℕ} (h : IsPiece P l) (r : ℕ) : IsPiece P (l.rotate r) where
  nodup := List.nodup_rotate.2 h.nodup
  lt x hx := h.lt x (List.mem_rotate.1 hx)
  three_le := by rw [List.length_rotate]; exact h.three_le
  edges k hk := by
    rw [List.length_rotate] at hk ⊢
    have hl : 0 < l.length := by omega
    rw [getD_rotate_of_lt r hk, getD_rotate_of_lt r (Nat.mod_lt _ hl)]
    have e : ((k + 1) % l.length + r) % l.length = ((k + r) % l.length + 1) % l.length := by
      rw [Nat.mod_add_mod, Nat.mod_add_mod, show k + 1 + r = k + r + 1 by omega]
    rw [e]
    exact h.edges _ (Nat.mod_lt _ hl)
  simple := by rw [subPoly_rotate]; exact simple_rotate _ _ h.simple
  not_boundary p hp := by
    rw [subPoly_rotate, filled_rotate] at hp; exact h.not_boundary p hp
  not_diag d hd p hp := by
    rw [subPoly_rotate, filled_rotate] at hp; exact h.not_diag d hd p hp
  filled_subset := by rw [subPoly_rotate, filled_rotate]; exact h.filled_subset

/-- **Triangulations are insensitive to the order of the triangles.** -/
theorem triangulates_perm {Q : Polygon} {T T' : List Polygon.Triangle} (h : Q.Triangulates T)
    (hp : List.Perm T T') : Q.Triangulates T' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun t ht => h1 t (hp.mem_iff.2 ht), by rw [← hp.length_eq]; exact h2, ?_,
    hp.pairwise h4 fun hd => hd.symm, hp.pairwise h5 fun he => by rw [inter_comm, he, inter_comm]⟩
  rw [← h3]
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, hp'⟩; exact ⟨t, hp.mem_iff.2 ht, hp'⟩
  · rintro ⟨t, ht, hp'⟩; exact ⟨t, hp.mem_iff.1 ht, hp'⟩

/-- A list with pairwise disjoint nonempty "interiors" has no two rotation-equivalent members. -/
theorem pairwise_not_rotate_of_disj {pcs : List (List ℕ)}
    (hs : ∀ m ∈ pcs, (subPoly P m).Simple)
    (hd : pcs.Pairwise fun m m' =>
      Disjoint (interior (subPoly P m).filled) (interior (subPoly P m').filled)) :
    pcs.Pairwise fun m m' => ∀ r, m' ≠ m.rotate r := by
  refine hd.imp_of_mem fun {m m'} hm _ hdisj r he => ?_
  obtain ⟨p, hp⟩ := interior_filled_nonempty (hs m hm)
  rw [he, subPoly_rotate, filled_rotate] at hdisj
  exact Set.disjoint_left.1 hdisj hp hp

end Assemble

/-! ### Cost -/

section Cost

variable {σ : ℝ}

/-- The number of wedge tests performed by the run, counted pessimistically as all the copies
of both endpoints at each step. -/
noncomputable def runCost (P : Polygon) (σ : ℝ) : LState → List (ℕ × ℕ) → ℕ
  | _, [] => 0
  | S, d :: D => (S.cop d.1).length + (S.cop d.2).length + runCost P σ (step P σ S d) D

/-- One step adds one copy of each endpoint. -/
theorem length_cop_step (S : LState) {d : ℕ × ℕ} (_hd : d.1 ≠ d.2) (v : ℕ) :
    ((step P σ S d).cop v).length =
      (S.cop v).length + (if d.1 = v ∨ d.2 = v then 1 else 0) := by
  show (upd (upd S.cop d.1 (S.cnt :: S.cop d.1)) d.2 ((S.cnt + 1) :: S.cop d.2) v).length = _
  simp only [upd]
  by_cases h2 : v = d.2
  · subst h2; simp
  · by_cases h1 : v = d.1
    · subst h1; simp [h2]
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right (by tauto)]; rfl

/-- **Cost bound.**  If every vertex has, together with its future incident diagonals, at most
`B` copies, then the run performs at most `2 B` wedge tests per diagonal. -/
theorem runCost_le {B : ℕ} : ∀ (D : List (ℕ × ℕ)) (S : LState), (∀ d ∈ D, d.1 ≠ d.2) →
    (∀ v, (S.cop v).length + D.countP (fun e => decide (e.1 = v ∨ e.2 = v)) ≤ B) →
    runCost P σ S D ≤ 2 * B * D.length := by
  intro D
  induction D with
  | nil => intro S _ _; simp [runCost]
  | cons d D ih =>
    intro S hne hB
    have hd := hne d List.mem_cons_self
    have h1 := hB d.1
    have h2 := hB d.2
    rw [List.countP_cons] at h1 h2
    have hrest := ih (step P σ S d) (fun e he => hne e (List.mem_cons_of_mem _ he)) (by
      intro v
      rw [length_cop_step S hd v]
      have := hB v
      rw [List.countP_cons] at this
      split_ifs at this ⊢ with h h' h' <;> simp_all; omega)
    show (S.cop d.1).length + (S.cop d.2).length + runCost P σ (step P σ S d) D ≤ _
    simp only [true_or, or_true, decide_true, ite_true] at h1 h2
    rw [List.length_cons, show 2 * B * (D.length + 1) = 2 * B * D.length + 2 * B by ring]
    omega

/-- The copies in the initial structure: one per vertex `< n`. -/
theorem length_cop_init (n v : ℕ) : ((initState n).cop v).length ≤ 1 := by
  show (if v < n then [v] else []).length ≤ 1
  split_ifs <;> simp

/-- **The final-stage input enumerates the inserted diagonals.** -/
theorem enumDiags_diagList {T : TrapTable} {C : List ChordRec} (hP : P.Simple)
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) : EnumDiags P (diagList P T C) where
  sound d hd := ((diagList_mem_iff hP hT hC d).1 hd).2
  complete d hd := by
    obtain ⟨h1, h2, hne⟩ := Chazelle.Mountain.allDiagonals_lt hP hd
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact Or.inl ((diagList_mem_iff hP hT hC d).2 ⟨h, Or.inl hd⟩)
    · exact Or.inr ((diagList_mem_iff hP hT hC d.swap).2
        ⟨h, Or.inr (by rw [Prod.swap_swap]; exact hd)⟩)
  distinct := (diagList_nodup P T C).imp_of_mem fun {d d'} hd hd' hne => by
    refine ⟨hne, fun e => ?_⟩
    have h1 := (diagList_lt hP hT hC hd).1
    have h2 := (diagList_lt hP hT hC hd').1
    rw [e] at h1
    simp only [Prod.fst_swap, Prod.snd_swap] at h1
    omega

end Cost

/-! ### The output: walking the final cycles -/

section Output

open Chazelle.Existence (WeakTriangulates)
open Chazelle.EarClip (relabelList)

/-- **Every cycle, walked from any of its nodes, is a piece.** -/
theorem isPiece_walk (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D) {S : LState}
    {cs : List (List ℕ)} (hR : Repr S cs)
    (hp : List.Perm (cs.map (List.map S.vtx)) (splitAll (List.range P.n) D)) {c : List ℕ}
    (hc : c ∈ cs) {i : ℕ} (hi : i < c.length) :
    IsPiece P ((walk S (c.getD i 0) c.length).map S.vtx) := by
  rw [walk_eq_rotate (hR.cyc c hc) hi, List.map_rotate]
  exact isPiece_rotate (hD.isPiece hP (hp.mem_iff.1 (List.mem_map_of_mem hc))) i

end Output

/-! ### Prefixes of the run and elementary invariants (used by the RAM simulation) -/

section Prefix

variable {σ : ℝ}

theorem runState_append (S : LState) (D D' : List (ℕ × ℕ)) :
    runState P σ S (D ++ D') = runState P σ (runState P σ S D) D' := by
  induction D generalizing S with
  | nil => rfl
  | cons d D ih => exact ih (step P σ S d)

theorem cnt_step (S : LState) (d : ℕ × ℕ) : (step P σ S d).cnt = S.cnt + 2 := rfl

theorem cnt_runState (S : LState) (D : List (ℕ × ℕ)) :
    (runState P σ S D).cnt = S.cnt + 2 * D.length := by
  induction D generalizing S with
  | nil => simp
  | cons d D ih => rw [runState_cons, ih, cnt_step, List.length_cons]; ring

theorem runCost_cons (S : LState) (d : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    runCost P σ S (d :: D) = (S.cop d.1).length + (S.cop d.2).length +
      runCost P σ (step P σ S d) D := rfl

/-- **Closure**: the links of the nodes stay among the nodes, the copies are nodes, the vertices
are `< n`, and there is at least one node. -/
structure Closed (S : LState) (n : ℕ) : Prop where
  pos : 0 < S.cnt
  nxt : ∀ z < S.cnt, S.nxt z < S.cnt
  prv : ∀ z < S.cnt, S.prv z < S.cnt
  vtx : ∀ z < S.cnt, S.vtx z < n
  cop : ∀ v, ∀ z ∈ S.cop v, z < S.cnt

theorem closed_init {n : ℕ} (hn : 0 < n) : Closed (initState n) n where
  pos := hn
  nxt z _ := Nat.mod_lt _ hn
  prv z _ := Nat.mod_lt _ hn
  vtx z hz := hz
  cop v z hz := by
    show z < n
    have : z ∈ (if v < n then [v] else []) := hz
    split_ifs at this with h
    · rw [List.mem_singleton] at this; omega
    · exact absurd this List.not_mem_nil

theorem selectLast_lt {p : ℕ → Bool} {l : List ℕ} {r N : ℕ} (hr : r < N) (hl : ∀ z ∈ l, z < N) :
    selectLast p l r < N := by
  induction l generalizing r with
  | nil => exact hr
  | cons a l ih =>
    rw [selectLast_cons]
    exact ih (by split_ifs; exacts [hl a List.mem_cons_self, hr])
      fun z hz => hl z (List.mem_cons_of_mem _ hz)

theorem findCopy_lt {S : LState} {n : ℕ} (hS : Closed S n) (v w : ℕ) :
    findCopy P σ S v w < S.cnt :=
  selectLast_lt hS.pos (hS.cop v)

/-- Closure passes through a step along a pair of vertices `< n`. -/
theorem Closed.step {S : LState} {n : ℕ} (hS : Closed S n) {d : ℕ × ℕ} (h1 : d.1 < n)
    (h2 : d.2 < n) : Closed (step P σ S d) n := by
  have hx := findCopy_lt (P := P) (σ := σ) hS d.1 d.2
  have hy := findCopy_lt (P := P) (σ := σ) hS d.2 d.1
  have hpx := hS.prv _ hx
  have hny := hS.nxt _ hy
  refine ⟨by show 0 < S.cnt + 2; omega, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_,
    fun v z hz => ?_⟩
  · show upd (upd (upd (upd S.nxt _ _) _ _) _ _) _ _ z < S.cnt + 2
    simp only [upd]
    have hz' : z < S.cnt + 2 := hz
    split_ifs
    · omega
    · omega
    · omega
    · omega
    · have := hS.nxt z (by omega); omega
  · show upd (upd (upd (upd S.prv _ _) _ _) _ _) _ _ z < S.cnt + 2
    simp only [upd]
    have hz' : z < S.cnt + 2 := hz
    split_ifs
    · omega
    · omega
    · omega
    · omega
    · have := hS.prv z (by omega); omega
  · show upd (upd S.vtx _ _) _ _ z < n
    simp only [upd]
    have hz' : z < S.cnt + 2 := hz
    split_ifs
    · exact h2
    · exact h1
    · exact hS.vtx z (by omega)
  · show z < S.cnt + 2
    have hz' : z ∈ upd (upd S.cop d.1 (S.cnt :: S.cop d.1)) d.2 ((S.cnt + 1) :: S.cop d.2) v := hz
    simp only [upd] at hz'
    split_ifs at hz'
    · rcases List.mem_cons.1 hz' with rfl | h
      · omega
      · have := hS.cop _ z h; omega
    · rcases List.mem_cons.1 hz' with rfl | h
      · omega
      · have := hS.cop _ z h; omega
    · have := hS.cop _ z hz'; omega

end Prefix

end

end Chazelle.Final
