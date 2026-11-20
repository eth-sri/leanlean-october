module

public import RequestProject.GenusOrdinaryPairCollapse
public import RequestProject.PositiveBoundaryCoordinates

@[expose] public section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]

variable (left right : List (GenusCollapsePair q))

theorem recorded_cut_data (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++ cellPair (Sum.inr σ) t :: right) :
    t.1.spx = σ.1 ∧ t.1.sgn = 0 := by
  have hi := (recordedGeometry (s := Sum.inr σ) (t := t) hsplit).incident
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    simp only [truncatedFaceIndex, spineInc] at hi
    split at hi <;> simp_all
  refine ⟨by simpa using congrArg freeSet he, ?_⟩
  funext v
  have hh := qCubeToCoordinate_parity t.1 v
  by_cases hv : v ∈ σ.1 <;> simp_all [posCube, hv]

/-- Every recorded cut-face pair satisfies the local collapse comparison. -/
theorem genus_recorded_cut_pair_stage_comparison
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    LoopComparison (genusCollapseStage q left)
      (genusCollapseStage q (left ++ [(qCubeToCoordinate t.1, Sum.inr σ.1)])) := by
  obtain ⟨hs, hpos⟩ := recorded_cut_data q left right σ t hsplit
  have hne := hs.symm ▸ σ.2.1
  have hσ : σ = fullCutCell t hne := Subtype.ext hs.symm
  subst σ
  have g := recordedGeometry (s := Sum.inr (fullCutCell t hne)) (t := t) hsplit
  exact g.comparison (positiveCutPuncturedBoundary_connectedIn t hne hpos g.top_dim)
    (positiveCutPuncturedBoundary_simplyConnectedIn t hne hpos g.top_dim)

end FiniteChains.Davis.Genus
