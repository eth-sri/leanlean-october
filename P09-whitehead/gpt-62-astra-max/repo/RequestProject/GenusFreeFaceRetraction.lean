module

public import RequestProject.GenusSpineCells
public import RequestProject.TruncatedCellIncidence
public import RequestProject.OrderComplexMaximalPath

@[expose] public section

/-! Homotopy reflection for deletion of an actual free face at a genus collapse stage. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

theorem genus_top_cell_maximal (t : QOld _)
    (ht : t.1.spx.card = 3) (x : GenusTruncatedCell q)
    (htx : (Sum.inl t) ≤ x) : x = Sum.inl t := by
  have hmax := genusTruncatedCell_dimension_le_three q x
  have hmono := truncatedCellDimension_monotone htx
  change t.1.spx.card ≤ truncatedCellDimension x at hmono
  have he : truncatedCellDimension (Sum.inl t) =
      truncatedCellDimension x := by
    change t.1.spx.card = truncatedCellDimension x
    omega
  exact (truncatedCell_eq_of_le_of_dimension_eq htx he).symm

/-- A top cube has a genuine old vertex on its boundary different from any deleted two-face.
Use the negative value on every free coordinate, so the removed positive vertex is avoided. -/
theorem genus_top_boundary_nonempty (f : GenusTruncatedCell q)
    (hf : truncatedCellDimension f = 2) (t : QOld _)
    (ht : t.1.spx.card = 3) :
    ∃ x : GenusTruncatedCell q, x ≠ f ∧ x < Sum.inl t := by
  classical
  let v : QCube (cmpRel (GenusVertex q)) := {
    spx := ∅
    sgn := fun j => if j ∈ t.1.spx then 1 else t.1.sgn j
    isSimplex := isSimplex_empty
    sgn_eq_zero := by simp }
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < t.1.spx.card)
  have hv : ¬ (v.spx = ∅ ∧ v.sgn = 0) := by
    rintro ⟨_, hs⟩
    have hh := congrFun hs j
    change (if j ∈ t.1.spx then 1 else t.1.sgn j) = 0 at hh
    simp_all
  let w : QOld _ := ⟨v, hv⟩
  have hw : (Sum.inl w : GenusTruncatedCell q) ≤ Sum.inl t := by
    refine ⟨Finset.empty_subset _, ?_⟩
    aesop
  have hdim : truncatedCellDimension (Sum.inl w) = 0 := rfl
  refine ⟨Sum.inl w, ?_, lt_of_le_of_ne hw ?_⟩
  · intro he
    simp_all
  · intro he
    have hh := congrArg truncatedCellDimension he
    change truncatedCellDimension _ = t.1.spx.card at hh
    omega

/-- The boundary of a later cube contains no face deleted in the prefix of the actual
chosen collapse. This prevents earlier steps from puncturing the next cube's boundary. -/
theorem genus_later_top_boundary_avoids_prefix_faces
    (left right : List _)
    (hl : genusChainCollapse q = left ++ right)
    (f : GenusTruncatedCell q) (t : QOld _)
    (ht : qCubeToCoordinate t.1 ∈ right.map Prod.fst)
    (hft : f ≤ Sum.inl t) : truncatedFaceIndex f ∉ left.map Prod.snd := by
  intro hf
  obtain ⟨p, hp, hpf⟩ := List.mem_map.mp hf
  obtain ⟨r, hr, hrt⟩ := List.mem_map.mp ht
  have hfullf : truncatedFaceIndex f ∈ (genusChainCollapse q).map Prod.snd := by
    rw [hl]
    exact List.mem_map.mpr ⟨p, List.mem_append.mpr (Or.inl hp), hpf⟩
  have hfullt : qCubeToCoordinate t.1 ∈ (genusChainCollapse q).map Prod.fst := by
    rw [hl]
    exact List.mem_map.mpr ⟨r, List.mem_append.mpr (Or.inr hr), hrt⟩
  have hL : t.1.spx ∈ (ASC.orderComplex (GenusVertex q)).faces := by
    intro a ha b hb _
    exact (isSimplex_cmpRel_iff.mp t.1.isSimplex) a ha b hb
  have hi := truncatedCell_inc_of_le f t hft (genus_removedFace_dimension q f hfullf) ((genus_oldCell_removed_iff_dimension_three q t).mp hfullt) hL
  have hc := genusChainCollapse_isPairCollapse q
  rw [hl] at hc
  have hn := hc.prefix_faces_avoid_suffix_tops hp hr
  grind

end FiniteChains.Davis.Genus
