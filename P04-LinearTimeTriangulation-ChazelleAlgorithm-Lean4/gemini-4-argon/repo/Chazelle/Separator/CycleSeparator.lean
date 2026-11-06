module

public import Chazelle.Separator.Cotree

/-!
# The fundamental-cycle separator (planar separators, part 3c)

Let `M` be a planar map with a rooted spanning tree `T` and vertex weights `w`.  Every vertex
`v` sends its weight to one face `fv v` around it.  For a non-tree dart `d`, `cross d` is the side
of the fundamental cycle of `d` entered through `d` (`Cotree.lean`), of weight `crossWeight w d`;
the two sides of an edge carry the whole weight (`crossWeight_add_opp`).

* **Centroid face** (`exists_centroid`): some face `f` has every side `cross d` entered through a
  non-tree dart `d` of `f` of weight at most half the total.  (Take a heavy side `cross d` with
  as few faces as possible; the face entered through `d` is a centroid, by the nesting of
  sides `cross_subset`.)
* **Separator of a face** (`sepSet f`): the vertices on the tree paths from the corners of `f`
  to the root.  Every vertex `v` off `sepSet f` lies on the far side of exactly one non-tree
  dart of `f` (`exists_label`, `label_unique`), and the two endpoints of an edge off
  `sepSet f` get the same dart (`label_adj`, the Jordan property of `Cotree.lean`).
* `exists_face_separator`: the resulting labelling, each class of weight `≤ W/2`.
* `card_sepSet_filter_le`: `sepSet f` has at most `deg f` vertices on each level.
* The packing lemma `exists_packing` and `exists_partition_of_labeling` turn a labelling
  with classes of weight `≤ 2W/3` into a partition `A, B, S` with no `A`–`B` edge.
* `cycle_separator`: **Lipton–Tarjan's Lemma 2, three-path form.**  A planar map whose faces have
  degree at most `3`, with a spanning tree of depth `≤ r`, has a separator `S` with
  `|S| ≤ 3 (r + 1)` whose removal leaves two parts of weight `≤ 2W/3` with no edge between them.
-/

namespace Chazelle.Separator

@[expose] public section

open Equiv Finset Relation

/-! ### Packing groups into two parts -/

section Packing

variable {ι : Type*}

end Packing

namespace CombMap

variable {V F D : Type*} (M : CombMap V F D)



namespace SpanTree

variable [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
variable {M} (T : SpanTree M)

/-! ### Weights of sides and the centroid face -/

/-! ### The separator of a face and the labelling -/

/-- The vertices on the tree paths from the corners of the face `f` to the root. -/
noncomputable def sepSet (f : F) : Finset V :=
  haveI := Classical.decPred (fun v : V => ∃ e, M.face e = f ∧ T.IsAnc v (M.vert e))
  Finset.univ.filter (fun v => ∃ e, M.face e = f ∧ T.IsAnc v (M.vert e))

omit [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F] in
/-- Membership in the separator of a face: an ancestor of a corner of the face. -/
theorem mem_sepSet {f : F} {v : V} : v ∈ T.sepSet f ↔ ∃ e, M.face e = f ∧ T.IsAnc v (M.vert e) := by
  simp [sepSet]

omit [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F] in
/-- A vertex off `sepSet f` is not on the root path of any corner of `f`. -/
theorem not_isAnc_of_notMem_sepSet {f : F} {v : V} (hv : v ∉ T.sepSet f) {e : D}
    (he : M.face e = f) : ¬ T.IsAnc v (M.vert e) := fun h => hv (T.mem_sepSet.mpr ⟨e, he, h⟩)

omit [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F] in
/-- A vertex off `sepSet f` is not on the root path of the head of a dart of `f`. -/
theorem not_isAnc_head_of_notMem_sepSet {f : F} {v : V} (hv : v ∉ T.sepSet f) {e : D}
    (he : M.face e = f) : ¬ T.IsAnc v (M.head e) := by
  rw [← M.vert_fperm]
  exact T.not_isAnc_of_notMem_sepSet hv (by rwa [M.face_fperm_apply])

omit [DecidableEq F] in
/-- The far sides of distinct non-tree darts of one face are disjoint. -/
theorem label_unique (hM : M.Planar) {d d' : D} (hd : d ∈ T.coDarts) (hd' : d' ∈ T.coDarts)
    (hf : M.face d' = M.face d) {g : F} (hg : g ∈ T.cross d) (hg' : g ∈ T.cross d') :
    d = d' := by
  by_contra hne
  have hsub := T.cross_subset hM (T.opp_mem_coDarts hd) hd' (by rwa [M.opp_opp])
    (by rw [M.opp_opp]; exact Ne.symm hne)
  exact T.notMem_cross_opp hM hd hg (hsub hg')

omit [DecidableEq D] [Fintype F] in
/-- The separator of a face has at most `deg f` vertices on each level (levels shifted by
`c`). -/
theorem card_sepSet_filter_shift_le (f : F) (c : ℕ) (I : Finset ℕ) :
    ((T.sepSet f).filter (fun v => T.level v + c ∈ I)).card ≤ M.faceDeg f * I.card := by
  classical
  set E := Finset.univ.filter (fun e => M.face e = f)
  have hsub : (T.sepSet f).filter (fun v => T.level v + c ∈ I) ⊆
      E.biUnion (fun e => Finset.univ.filter
        (fun v => T.IsAnc v (M.vert e) ∧ T.level v + c ∈ I)) := by
    intro v hv
    simp only [Finset.mem_filter, mem_sepSet] at hv
    obtain ⟨⟨e, he, hanc⟩, hl⟩ := hv
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, E]
    exact ⟨e, he, hanc, hl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [faceDeg, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun e _ => ?_)
  refine Finset.card_le_card_of_injOn (fun v => T.level v + c) ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
    exact hv.2
  · intro v hv v' hv' hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv hv'
    exact T.eq_of_isAnc_of_level_eq hv.1 hv'.1 (by simpa using hl)

end SpanTree

end CombMap

end

end Chazelle.Separator
