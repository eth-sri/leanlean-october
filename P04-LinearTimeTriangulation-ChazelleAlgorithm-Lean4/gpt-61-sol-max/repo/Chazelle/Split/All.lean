module

public meta import Chazelle.Arithmetic

public import Chazelle.Split.Once

/-!
# Splitting a sub-polygon along a system of non-crossing diagonals

A *diagonal system* for `(P, l)` (`DiagSystem P l D`): `subPoly P l` is simple, every `d ∈ D` is
an interior diagonal of it (`IsDiag P l d`), and the members of `D` are pairwise non-crossing
(`NonCross P`: their segments meet at most in common endpoints; in particular no two members of
`D` name the same segment).

`splitAll l D` cuts `l` along the head diagonal `d` of `D` (pieces `splitFst l d` and
`splitSnd l d`), sends each remaining diagonal to the first piece when both its endpoints are
entries of the first piece (`diagsFst`) and to the second piece otherwise (`diagsSnd`), and
recurses (well-founded recursion on `D.length`).  `combineTri T l D` assembles triangulations
`T m` of the output pieces `m` (in positions of `m`) into triangles in positions of `l`.

## Main results

* `pieceOf_splitAll`: every output piece `m` is a simple sub-polygon whose entries are entries of
  `l`, whose cyclic edges are cyclic edges of `l` or members of `D` (either orientation), whose
  interior avoids the boundary of `subPoly P l` and every segment of `D`, and whose filled region
  lies in that of `subPoly P l` (`PieceOf P l D m`).
* `weakTriangulates_combineTri`: if every output piece `m` is weakly triangulated by `T m`, then
  `combineTri T l D` weakly triangulates `subPoly P l`; `map_relabelList_combineTri`: in original
  indices it is the concatenation of the `T m` relabelled by `relabelList m`; both packaged as
  `exists_weakTriangulates_of_splitAll`.
* `length_splitAll`: there are `D.length + 1` pieces; `sum_length_splitAll`: their lengths add up
  to `l.length + 2 * D.length`.
-/

namespace Chazelle.Split

@[expose] public section

open Set
open Chazelle.Jordan (interior_filled)
open Chazelle.Existence (WeakTriangulates relabel)
open Chazelle.EarClip (subPoly n_subPoly relabelList)

/-! ### The recursion -/

/-- Both endpoints of `d` are entries of `m` (as a Boolean test). -/
def sideTest (m : List ℕ) (d : ℕ × ℕ) : Bool := decide (d.1 ∈ m) && decide (d.2 ∈ m)

theorem sideTest_eq_true {m : List ℕ} {d : ℕ × ℕ} :
    sideTest m d = true ↔ d.1 ∈ m ∧ d.2 ∈ m := by
  simp [sideTest]

section
variable (l : List ℕ) (d : ℕ × ℕ) (D : List (ℕ × ℕ))
include l d D
/-- The diagonals of `D` sent to the first piece of `l` cut along `d`: those with both endpoints
in `splitFst l d`. -/
def diagsFst : List (ℕ × ℕ) :=
  D.filter (sideTest (splitFst l d))

/-- The diagonals of `D` sent to the second piece of `l` cut along `d`: all the others. -/
def diagsSnd : List (ℕ × ℕ) :=
  D.filter (fun d' => !sideTest (splitFst l d) d')


end

section
variable {l : List ℕ} {d d' : ℕ × ℕ} {D : List (ℕ × ℕ)}
theorem mem_diagsFst :
    d' ∈ diagsFst l d D ↔ d' ∈ D ∧ d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d := by
  rw [diagsFst, List.mem_filter, sideTest_eq_true]

theorem mem_diagsSnd :
    d' ∈ diagsSnd l d D ↔ d' ∈ D ∧ ¬ (d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d) := by
  rw [diagsSnd, List.mem_filter, Bool.not_eq_true', ← sideTest_eq_true, Bool.not_eq_true]


end

/-- **Splitting `l` along all the diagonals of `D`**: cut along the head diagonal, distribute the
remaining diagonals to the two pieces, and recurse. -/
def splitAll : List ℕ → List (ℕ × ℕ) → List (List ℕ)
  | l, [] => [l]
  | l, d :: D =>
    splitAll (splitFst l d) (diagsFst l d D) ++ splitAll (splitSnd l d) (diagsSnd l d D)
termination_by _ D => D.length
decreasing_by
  all_goals core_grind

/-- **Assembling triangulations of the pieces.**  Given triangles `T m` for each piece `m` (in
positions of `m`), the triangles in positions of `l`, following the recursion of `splitAll`. -/
def combineTri (T : List ℕ → List Polygon.Triangle) :
    List ℕ → List (ℕ × ℕ) → List Polygon.Triangle
  | l, [] => T l
  | l, d :: D =>
    (combineTri T (splitFst l d) (diagsFst l d D)).map (relabel (l.idxOf d.1) l.length) ++
      (combineTri T (splitSnd l d) (diagsSnd l d D)).map (relabel (l.idxOf d.2) l.length)
termination_by _ D => D.length
decreasing_by
  all_goals core_grind

section
variable (l : List ℕ)
@[simp] theorem splitAll_nil : splitAll l [] = [l] := by
  rw [splitAll]

theorem splitAll_cons (d : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    splitAll l (d :: D) =
      splitAll (splitFst l d) (diagsFst l d D) ++ splitAll (splitSnd l d) (diagsSnd l d D) := by
  rw [splitAll]


end

section
variable (T : List ℕ → List Polygon.Triangle) (l : List ℕ)
@[simp] theorem combineTri_nil :
    combineTri T l [] = T l := by
  rw [combineTri]

theorem combineTri_cons (d : ℕ × ℕ)
    (D : List (ℕ × ℕ)) :
    combineTri T l (d :: D) =
      (combineTri T (splitFst l d) (diagsFst l d D)).map (relabel (l.idxOf d.1) l.length) ++
        (combineTri T (splitSnd l d) (diagsSnd l d D)).map (relabel (l.idxOf d.2) l.length) := by
  rw [combineTri]


end

/-- Induction principle following the recursion of `splitAll`. -/
theorem splitAll_induction {motive : List ℕ → List (ℕ × ℕ) → Prop}
    (nil : ∀ l, motive l [])
    (cons : ∀ l d D, motive (splitFst l d) (diagsFst l d D) →
      motive (splitSnd l d) (diagsSnd l d D) → motive l (d :: D)) :
    ∀ l D, motive l D := by
  suffices H : ∀ N l D, D.length ≤ N → motive l D from fun l D => H _ l D le_rfl
  intro N
  induction N with
  | zero =>
    simp_all
  | succ N ih =>
    intro l D hD
    cases D with
    | nil => exact nil l
    | cons d D =>
      rw [List.length_cons] at hD
      exact cons l d D (ih _ _ ((List.length_filter_le _ _).trans (by omega)))
        (ih _ _ ((List.length_filter_le _ _).trans (by omega)))

/-! ### Diagonal systems -/

/-- **A diagonal system for `(P, l)`**: `subPoly P l` is simple, every member of `D` is an
interior diagonal of it, and the members of `D` are pairwise non-crossing. -/
structure DiagSystem (P : Polygon) (l : List ℕ) (D : List (ℕ × ℕ)) : Prop where
  simple : (subPoly P l).Simple
  diag : ∀ d ∈ D, IsDiag P l d
  noncross : D.Pairwise (NonCross P)

variable {P : Polygon}

section System

variable {l : List ℕ} {d : ℕ × ℕ} {D : List (ℕ × ℕ)}

/-- The head diagonal of a system splits `l` into a `SplitPair`. -/
theorem DiagSystem.splitPair (h : DiagSystem P l (d :: D)) :
    SplitPair P l d (splitFst l d) (splitSnd l d) :=
  splitPair_split h.simple (h.diag d List.mem_cons_self)

section
variable (h : DiagSystem P l (d :: D)) {d' : ℕ × ℕ} (hd' : d' ∈ D)
include h hd'
theorem DiagSystem.tail_isDiag :
    IsDiag P l d' :=
  h.diag d' (List.mem_cons_of_mem _ hd')

theorem DiagSystem.tail_nonCross :
    NonCross P d d' :=
  (List.pairwise_cons.1 h.noncross).1 d' hd'

/-- A tail diagonal whose endpoints are not both in the first piece is a diagonal of the second
piece. -/
theorem DiagSystem.isDiag_snd
    (hmem : ¬ (d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d)) : IsDiag P (splitSnd l d) d' :=
  h.splitPair.isDiag_snd h.simple (h.tail_isDiag hd') (h.tail_nonCross hd') hmem

/-- A tail diagonal whose endpoints are both in the first piece is a diagonal of the first
piece. -/
theorem DiagSystem.isDiag_fst
    (hmem : d'.1 ∈ splitFst l d ∧ d'.2 ∈ splitFst l d) : IsDiag P (splitFst l d) d' :=
  h.splitPair.isDiag_fst h.simple (h.tail_isDiag hd') (h.tail_nonCross hd') hmem


end

section
variable (h : DiagSystem P l (d :: D))
include h
/-- The system passes to the first piece. -/
theorem DiagSystem.fst :
    DiagSystem P (splitFst l d) (diagsFst l d D) where
  simple := h.splitPair.simple₁
  diag d' hd' := by
    rw [mem_diagsFst] at hd'
    exact h.isDiag_fst hd'.1 hd'.2
  noncross := (List.pairwise_cons.1 h.noncross).2.filter _

/-- The system passes to the second piece. -/
theorem DiagSystem.snd :
    DiagSystem P (splitSnd l d) (diagsSnd l d D) where
  simple := h.splitPair.simple₂
  diag d' hd' := by
    rw [mem_diagsSnd] at hd'
    exact h.isDiag_snd hd'.1 hd'.2
  noncross := (List.pairwise_cons.1 h.noncross).2.filter _


end

end System

/-! ### The pieces -/

/-- The properties of an output piece `m` of splitting `l` along `D`. -/
structure PieceOf (P : Polygon) (l : List ℕ) (D : List (ℕ × ℕ)) (m : List ℕ) : Prop where
  simple : (subPoly P m).Simple
  sub : ∀ x ∈ m, x ∈ l
  edges : ∀ k < m.length, CycEdge l (m.getD k 0) (m.getD ((k + 1) % m.length) 0) ∨
    (m.getD k 0, m.getD ((k + 1) % m.length) 0) ∈ D ∨
      (m.getD ((k + 1) % m.length) 0, m.getD k 0) ∈ D
  not_boundary : ∀ p ∈ interior (subPoly P m).filled, p ∉ (subPoly P l).boundary
  not_diag : ∀ d ∈ D, ∀ p ∈ interior (subPoly P m).filled, p ∉ pairSeg P d
  filled_subset : (subPoly P m).filled ⊆ (subPoly P l).filled

/-- With no diagonals, `l` itself is the piece. -/
theorem pieceOf_self {l : List ℕ} (hQ : (subPoly P l).Simple) : PieceOf P l [] l where
  simple := hQ
  sub _ h := h
  edges k hk := Or.inl (cycEdge_self l hk)
  not_boundary p hp := by
    rw [interior_filled hQ] at hp
    exact hp.2
  not_diag _ h := absurd h List.not_mem_nil
  filled_subset := subset_rfl

/-- **Lifting a piece through one split.**  A piece of the first piece `l₁` of `l` cut along `d`,
for a diagonal list `D₁ ⊆ D` such that the diagonals of `D` not in `D₁` lie in the second piece,
is a piece of `l` for `d :: D`. -/
theorem PieceOf.lift {l l₁ l₂ : List ℕ} {d : ℕ × ℕ} {D D₁ : List (ℕ × ℕ)}
    (hs : SplitPair P l d l₁ l₂) (hsub : ∀ d' ∈ D₁, d' ∈ D)
    (hrest : ∀ d' ∈ D, d' ∉ D₁ → pairSeg P d' ⊆ (subPoly P l₂).filled)
    {m : List ℕ} (hm : PieceOf P l₁ D₁ m) : PieceOf P l (d :: D) m where
  simple := hm.simple
  sub x hx := hs.sub₁ x (hm.sub x hx)
  edges k hk := by
    rcases hm.edges k hk with h | h | h
    · rcases hs.edges₁ _ _ h with h' | h' | h'
      · simp_all
      · simp_all
      grind
    · simp_all
    simp_all
  not_boundary p hp :=
    hs.interior_not_mem_boundary (interior_mono hm.filled_subset hp)
  not_diag d' hd' p hp := by
    have hp₁ := interior_mono hm.filled_subset hp
    rcases List.mem_cons.1 hd' with rfl | hd'
    · exact hs.interior_not_mem_chord hp₁
    · by_cases h₁ : d' ∈ D₁
      · exact hm.not_diag d' h₁ p hp
      · exact fun h => hs.interior_not_mem_filled hp₁ (hrest d' hd' h₁ h)
  filled_subset := hm.filled_subset.trans hs.filled_subset

/-- **Properties of the output pieces.**  Every piece `m` of `splitAll l D`, for a diagonal
system `D` of `(P, l)`, is a simple sub-polygon whose entries are entries of `l`, whose cyclic
edges are cyclic edges of `l` or members of `D` (in either orientation), whose interior avoids the
boundary of `subPoly P l` and every segment of `D`, and whose filled region lies in that of
`subPoly P l`. -/
theorem pieceOf_splitAll {l : List ℕ} {D : List (ℕ × ℕ)} (h : DiagSystem P l D) :
    ∀ m ∈ splitAll l D, PieceOf P l D m := by
  revert h
  refine splitAll_induction (motive := fun l D => DiagSystem P l D →
    ∀ m ∈ splitAll l D, PieceOf P l D m) ?_ ?_ l D
  · intro l h m hm
    rw [splitAll_nil, List.mem_singleton] at hm
    subst hm
    exact pieceOf_self h.simple
  · intro l d D ih₁ ih₂ h m hm
    rw [splitAll_cons, List.mem_append] at hm
    rcases hm with hm | hm
    · refine (ih₁ h.fst m hm).lift h.splitPair (fun d' hd' => (mem_diagsFst.1 hd').1) ?_
      intro d' hd' hn
      rw [mem_diagsFst, not_and] at hn
      exact (h.isDiag_snd hd' (hn hd')).2.2.2.2
    · refine (ih₂ h.snd m hm).lift h.splitPair.symm (fun d' hd' => (mem_diagsSnd.1 hd').1) ?_
      intro d' hd' hn
      rw [mem_diagsSnd, not_and, not_not] at hn
      exact (h.isDiag_fst hd' (hn hd')).2.2.2.2

/-! ### Combining triangulations -/

section
variable {l : List ℕ} {D : List (ℕ × ℕ)} (h : DiagSystem P l D) {T : List ℕ → List Polygon.Triangle} (hT : ∀ m ∈ splitAll l D, WeakTriangulates (subPoly P m) (T m))
include h hT
/-- **Combination.**  If every piece `m` of `splitAll l D` (for a diagonal system `D`) is weakly
triangulated by `T m` (in positions of `m`), then `combineTri T l D` weakly triangulates
`subPoly P l` (in positions of `l`). -/
theorem weakTriangulates_combineTri :
    WeakTriangulates (subPoly P l) (combineTri T l D) := by
  revert h hT
  refine splitAll_induction (motive := fun l D => DiagSystem P l D →
    (∀ m ∈ splitAll l D, WeakTriangulates (subPoly P m) (T m)) →
      WeakTriangulates (subPoly P l) (combineTri T l D)) ?_ ?_ l D
  · simp_all
  · intro l d D ih₁ ih₂ h hT
    rw [combineTri_cons]
    exact weakTriangulates_split h.simple (h.diag d List.mem_cons_self)
      (ih₁ h.fst fun m hm => hT m (by simp_all [splitAll_cons] ))
      (ih₂ h.snd fun m hm => hT m (by simp_all [splitAll_cons] ))

/-- **The combined triangulation in original indices** is the concatenation, over the pieces
`m` of `splitAll l D`, of the triangles `T m` relabelled to original indices by
`relabelList m`. -/
theorem map_relabelList_combineTri :
    (combineTri T l D).map (relabelList l) =
      (splitAll l D).flatMap (fun m => (T m).map (relabelList m)) := by
  revert h hT
  refine splitAll_induction (motive := fun l D => DiagSystem P l D →
    (∀ m ∈ splitAll l D, WeakTriangulates (subPoly P m) (T m)) →
      (combineTri T l D).map (relabelList l) =
        (splitAll l D).flatMap (fun m => (T m).map (relabelList m))) ?_ ?_ l D
  · simp_all
  · intro l d D ih₁ ih₂ h hT
    have hd := h.diag d List.mem_cons_self
    have hT₁ : ∀ m ∈ splitAll (splitFst l d) (diagsFst l d D),
        WeakTriangulates (subPoly P m) (T m) :=
      fun m hm => hT m (by simp_all [splitAll_cons] <;> omega_nf)
    have hT₂ : ∀ m ∈ splitAll (splitSnd l d) (diagsSnd l d D),
        WeakTriangulates (subPoly P m) (T m) :=
      fun m hm => hT m (by simp_all [splitAll_cons] <;> omega_nf)
    have hw₁ := weakTriangulates_combineTri h.fst hT₁
    have hw₂ := weakTriangulates_combineTri h.snd hT₂
    rw [combineTri_cons, splitAll_cons, List.flatMap_append, List.map_append, List.map_map,
      List.map_map, ← ih₁ h.fst hT₁, ← ih₂ h.snd hT₂]
    congr 1
    · apply List.map_congr_left
      intro t ht
      have hb := index_lt_of_weak hw₁ ht
      rw [n_subPoly] at hb
      exact relabelList_relabel_fst hd.1 hd.2.1 hd.2.2.1 hb
    · apply List.map_congr_left
      intro t ht
      have hb := index_lt_of_weak hw₂ ht
      rw [n_subPoly] at hb
      exact relabelList_relabel_snd hd.1 hd.2.1 hd.2.2.1 hb

/-! ### Sizes -/


end

end

end Chazelle.Split
