module

public import RequestProject.GenusFreeFaceRetraction
public import RequestProject.OrdinaryTruncatedBoundary
public import RequestProject.GenusCollapseStages

@[expose] public section

/-! A complete elementary collapse comparison for an ordinary genus-block cube. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

/-- Dimensions and nonpositive corner of a recorded old-face pair. -/
theorem genus_old_pair_data
    (left right : List (GenusCollapsePair q))
    (f t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right)) :
    f.1.spx.card = 2 ∧ t.1.spx.card = 3 ∧ t.1.sgn ≠ 0 := by
  have hp : (qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) ∈ genusChainCollapse q := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  have d := genus_pair_data q (s := Sum.inl f) hsplit
  have hordinary : t.1.sgn ≠ 0 := by
    intro hs
    apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1)
      (qCubeToCoordinate f.1) hp
    simpa only [freeSet_qCubeToCoordinate] using qCubeToCoordinate_sgn_zero t.1 hs
  exact ⟨d.dim_face, d.dim_top, hordinary⟩

end FiniteChains.Davis.Genus
