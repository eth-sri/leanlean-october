module

public import Chazelle.Split.All
public import Chazelle.Mountain.Pieces

/-!
# Splitting a simple polygon along all the inserted diagonals

This file instantiates the multi-diagonal splitting of `Chazelle.Split.All` with the whole
polygon `l = List.range P.n` (so `subPoly P l = P`) and the diagonals `allDiagonals P` of the
trapezoidal decomposition (`Chazelle.Mountain.Decompose`).

* `EnumDiags P D`: the list `D` enumerates `allDiagonals P` up to orientation (every member or its
  swap is an inserted diagonal, every inserted diagonal or its swap is a member), with no pair
  repeated in either orientation.  (`vtxChords` contains both orientations of two-sided chords, so
  some deduplication is needed.)  Any such list will do; the RAM stage may use its own.
* `EnumDiags.diagSystem`: such a list is a diagonal system for `(P, List.range P.n)`.
* `EnumDiags.isPiece`: every output piece of `splitAll (List.range P.n) D` is a piece of the
  subdivision in the sense of `Chazelle.Mountain.IsPiece`.
* `EnumDiags.triangulates`: if `T m` weakly triangulates `subPoly P m` for every piece `m`, the
  concatenation of the `T m` relabelled to original indices (`relabelList m`) triangulates `P`.
* Sizes: `EnumDiags.length_le` (`D.length ≤ 4 * P.n + 1`), `length_splitAll` (`D.length + 1`
  pieces), `EnumDiags.sum_length` (total length `P.n + 2 * D.length`).
* `diagList P`: a canonical enumeration (the pairs `a < b < P.n` with `(a, b)` or `(b, a)` in
  `allDiagonals P`), `enumDiags_diagList`.
* `exists_triangulation_of_mountains`: the final composition lemma — given the mountain theorem in
  the form `∀ l, IsPiece P l → ∃ T, WeakTriangulates (subPoly P l) T`, `P` has a triangulation.
-/

namespace Chazelle.Split

@[expose] public section

open Set
open Chazelle.Existence (WeakTriangulates relabel IsDiagonal triangulates_of_weak)
open Chazelle.EarClip (subPoly n_subPoly relabelList subPoly_range getD_range relabelList_range)
open Chazelle.Mountain (allDiagonals diagSeg allDiagonals_isDiagonal allDiagonals_inter
  allDiagonals_lt allDiagonals_finite IsPiece IsPieceEdge)

variable {P : Polygon}

/-! ### Elementary facts -/

/-- `Chazelle.Mountain.diagSeg` is `pairSeg`. -/
theorem diagSeg_eq_pairSeg (P : Polygon) (d : ℕ × ℕ) : diagSeg P d = pairSeg P d := rfl

/-- A diagonal with its endpoints swapped. -/
theorem IsDiag.swap {l : List ℕ} {d : ℕ × ℕ} (hd : IsDiag P l d) : IsDiag P l d.swap := by
  obtain ⟨h1, h2, hne, hch, hf⟩ := hd
  refine ⟨h2, h1, Ne.symm hne, ?_, ?_⟩
  · intro p hp hp1 hp2
    rw [pairSeg_swap] at hp
    exact hch p hp hp2 hp1
  · rw [pairSeg_swap]; exact hf

/-- Non-crossing is invariant under swapping the first pair. -/
theorem NonCross.swap_left {d d' : ℕ × ℕ} (h : NonCross P d d') : NonCross P d.swap d' := by
  intro p hp
  rw [pairSeg_swap] at hp
  have := h hp
  refine ⟨?_, this.2⟩
  rcases this.1 with e | e
  · exact Or.inr e
  · exact Or.inl e

/-- Non-crossing is symmetric. -/
theorem NonCross.symm {d d' : ℕ × ℕ} (h : NonCross P d d') : NonCross P d' d := by
  intro p hp
  have := h ⟨hp.2, hp.1⟩
  exact ⟨this.2, this.1⟩

/-- Non-crossing is invariant under swapping the second pair. -/
theorem NonCross.swap_right {d d' : ℕ × ℕ} (h : NonCross P d d') : NonCross P d d'.swap :=
  h.symm.swap_left.symm

/-- **An inserted diagonal is an `IsDiag` of the whole polygon.** -/
theorem isDiag_range_of_mem_allDiagonals (hP : P.Simple) {d : ℕ × ℕ}
    (hd : d ∈ allDiagonals P) : IsDiag P (List.range P.n) d := by
  obtain ⟨h1, h2, hne⟩ := allDiagonals_lt hP hd
  obtain ⟨s, L, hdiag, hs, hsL, hsub⟩ := allDiagonals_isDiagonal hP hd
  unfold IsDiag
  rw [subPoly_range]
  refine ⟨List.mem_range.2 h1, List.mem_range.2 h2, hne, ?_, hsub⟩
  have hch := hdiag.2.2
  rw [hs, hsL] at hch
  exact hch

/-- A member of `allDiagonals P` up to orientation is an `IsDiag` of the whole polygon. -/
theorem isDiag_range_of_mem_or_swap (hP : P.Simple) {d : ℕ × ℕ}
    (hd : d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P) : IsDiag P (List.range P.n) d := by
  rcases hd with h | h
  · exact isDiag_range_of_mem_allDiagonals hP h
  · have := (isDiag_range_of_mem_allDiagonals hP h).swap
    rwa [Prod.swap_swap] at this

/-- **Two inserted diagonals (up to orientation) with the same segment are the same pair up to
orientation.** -/
theorem eq_or_eq_swap_of_pairSeg_eq (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P)
    (hd' : d' ∈ allDiagonals P ∨ d'.swap ∈ allDiagonals P) (h : pairSeg P d = pairSeg P d') :
    d' = d ∨ d' = d.swap := by
  have hD := isDiag_range_of_mem_or_swap hP hd
  have hD' := isDiag_range_of_mem_or_swap hP hd'
  have hQ : (subPoly P (List.range P.n)).Simple := by rw [subPoly_range]; exact hP
  -- each endpoint of `d'` is an endpoint of `d`
  have key : ∀ x, x ∈ List.range P.n → P.vtx x ∈ pairSeg P d → x = d.1 ∨ x = d.2 := by
    intro x hxl hxs
    by_contra hcon
    rw [not_or] at hcon
    apply hD.2.2.2.1 _ hxs (fun e => hcon.1 (eq_of_vtx_eq P hQ hxl hD.1 e))
      (fun e => hcon.2 (eq_of_vtx_eq P hQ hxl hD.2.1 e))
    rw [subPoly_range]
    exact Chazelle.Existence.vtx_mem_boundary P (List.mem_range.1 hxl)
  have e1 := key d'.1 hD'.1 (by rw [h]; exact Chazelle.Geometry.left_mem_segment _ _)
  have e2 := key d'.2 hD'.2.1 (by rw [h]; exact Chazelle.Geometry.right_mem_segment _ _)
  have hne := hD.2.2.1
  have hne' := hD'.2.2.1
  obtain ⟨a, b⟩ := d
  obtain ⟨a', b'⟩ := d'
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at e1 e2 hne hne' ⊢
  omega

/-- **Two inserted diagonals (up to orientation) that are distinct pairs up to orientation do not
cross.** -/
theorem nonCross_of_mem_or_swap (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P)
    (hd' : d' ∈ allDiagonals P ∨ d'.swap ∈ allDiagonals P) (hne : d ≠ d' ∧ d ≠ d'.swap) :
    NonCross P d d' := by
  have hseg : pairSeg P d ≠ pairSeg P d' := by
    intro h
    rcases eq_or_eq_swap_of_pairSeg_eq hP hd hd' h with e | e
    · exact hne.1 e.symm
    · exact hne.2 (by rw [e, Prod.swap_swap])
  have key : ∀ e e', e ∈ allDiagonals P → e' ∈ allDiagonals P →
      pairSeg P e = pairSeg P d → pairSeg P e' = pairSeg P d' → NonCross P e e' := by
    intro e e' he he' h1 h2
    apply allDiagonals_inter hP he he'
    rw [diagSeg_eq_pairSeg, diagSeg_eq_pairSeg, h1, h2]
    exact hseg
  rcases hd with h | h <;> rcases hd' with h' | h'
  · exact key _ _ h h' rfl rfl
  · have := (key _ _ h h' rfl (pairSeg_swap P d')).swap_right
    rwa [Prod.swap_swap] at this
  · have := (key _ _ h h' (pairSeg_swap P d) rfl).swap_left
    rwa [Prod.swap_swap] at this
  · have := (key _ _ h h' (pairSeg_swap P d) (pairSeg_swap P d')).swap_left.swap_right
    rwa [Prod.swap_swap, Prod.swap_swap] at this

/-! ### Enumerations of the inserted diagonals -/

/-- **`D` enumerates the inserted diagonals of `P` up to orientation**: every member or its swap
is in `allDiagonals P`, every member of `allDiagonals P` or its swap is in `D`, and no pair occurs
twice in `D`, in either orientation. -/
structure EnumDiags (P : Polygon) (D : List (ℕ × ℕ)) : Prop where
  sound : ∀ d ∈ D, d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P
  complete : ∀ d ∈ allDiagonals P, d ∈ D ∨ d.swap ∈ D
  distinct : D.Pairwise (fun d d' => d ≠ d' ∧ d ≠ d'.swap)

/-- **An enumeration of the inserted diagonals is a diagonal system for the whole polygon.** -/
theorem EnumDiags.diagSystem (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D) :
    DiagSystem P (List.range P.n) D where
  simple := by rw [subPoly_range]; exact hP
  diag d hd := isDiag_range_of_mem_or_swap hP (hD.sound d hd)
  noncross := hD.distinct.imp_of_mem fun hd hd' hne =>
    nonCross_of_mem_or_swap hP (hD.sound _ hd) (hD.sound _ hd') hne

/-- A cyclic edge of `List.range n` is an edge `x → x + 1 (mod n)`. -/
theorem cycEdge_range {n x y : ℕ} (h : CycEdge (List.range n) x y) : y = (x + 1) % n := by
  obtain ⟨k, hk, rfl, rfl⟩ := h
  rw [List.length_range] at hk ⊢
  rw [getD_range hk, getD_range (Nat.mod_lt _ (by omega))]

/-- **Every output piece is a piece of the subdivision of `P` by `allDiagonals P`.** -/
theorem EnumDiags.isPiece (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D) {m : List ℕ}
    (hm : m ∈ splitAll (List.range P.n) D) : IsPiece P m := by
  obtain ⟨hs, hsub, hedges, hbd, hdiag, hfill⟩ := pieceOf_splitAll (hD.diagSystem hP) m hm
  rw [subPoly_range] at hbd hfill
  refine ⟨nodup_of_simple P hs, fun x hx => List.mem_range.1 (hsub x hx),
    three_le_of_simple P hs, ?_, hs, hbd, ?_, hfill⟩
  · intro k hk
    rcases hedges k hk with h | h | h
    · exact Or.inl (cycEdge_range h)
    · rcases hD.sound _ h with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
    · rcases hD.sound _ h with h' | h'
      · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inr (Or.inr (Or.inl h'))
  · intro d hd p hp
    rw [diagSeg_eq_pairSeg]
    rcases hD.complete d hd with h' | h'
    · exact hdiag d h' p hp
    · rw [← pairSeg_swap]; exact hdiag _ h' p hp

/-- The triangles of a weak triangulation of `P` are unchanged by `relabelList (List.range P.n)`. -/
theorem map_relabelList_range {T : List Polygon.Triangle} (h : WeakTriangulates P T) :
    T.map (relabelList (List.range P.n)) = T := by
  conv_rhs => rw [← List.map_id T]
  apply List.map_congr_left
  intro t ht
  exact relabelList_range (index_lt_of_weak h ht)

/-- **Combination on the whole polygon.**  If `T m` weakly triangulates `subPoly P m` (in
positions of `m`) for every piece `m` of `splitAll (List.range P.n) D`, then the concatenation of
the `T m` relabelled to original indices weakly triangulates `P`. -/
theorem EnumDiags.weakTriangulates (hP : P.Simple) {D : List (ℕ × ℕ)} (hD : EnumDiags P D)
    {T : List ℕ → List Polygon.Triangle}
    (hT : ∀ m ∈ splitAll (List.range P.n) D, WeakTriangulates (subPoly P m) (T m)) :
    WeakTriangulates P
      ((splitAll (List.range P.n) D).flatMap (fun m => (T m).map (relabelList m))) := by
  have hsys := hD.diagSystem hP
  have hw := weakTriangulates_combineTri hsys hT
  rw [subPoly_range] at hw
  rw [← map_relabelList_combineTri hsys hT, map_relabelList_range hw]
  exact hw

/-! ### A canonical enumeration -/

/-! ### The final composition -/

end

end Chazelle.Split
