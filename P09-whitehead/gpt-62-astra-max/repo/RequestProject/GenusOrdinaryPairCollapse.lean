module


public import RequestProject.OrdinaryTruncatedBoundary
public import RequestProject.GenusCollapseStages

@[expose] public section

/-! A complete elementary collapse comparison for an ordinary genus-block cube. -/
namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

variable (left right : List (GenusCollapsePair q)) (f t : QOld (cmpRel (GenusVertex q)))

theorem recorded_old_sign
    (hsplit : genusChainCollapse q = left ++ cellPair (Sum.inl f) t :: right) : t.1.sgn ≠ 0 := by
  intro he
  apply genusChainCollapse_old_face_nonpositive q (qCubeToCoordinate t.1) (qCubeToCoordinate f.1)
    (by simp [hsplit, cellPair, truncatedFaceIndex])
  simpa only [freeSet_qCubeToCoordinate] using qCubeToCoordinate_sgn_zero t.1 he

/-- Every old-face pair in the chosen collapse satisfies the ordinary comparison, with
dimension and nonpositive-corner conditions derived from the actual recorded pair. -/
theorem genus_old_pair_stage_comparison
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1)) :: right)) :
    LoopComparison (genusCollapseStage q left)
      (genusCollapseStage q
        (left ++ [(qCubeToCoordinate t.1, Sum.inl (qCubeToCoordinate f.1))])) := by
  have g := recordedGeometry (s := Sum.inl f) hsplit
  have h := recorded_old_sign q left right f t hsplit
  exact g.comparison (ordinaryTruncatedBoundary_connectedIn h g.incident)
    (ordinaryTruncatedBoundary_simplyConnectedIn h g.incident)

end FiniteChains.Davis.Genus
