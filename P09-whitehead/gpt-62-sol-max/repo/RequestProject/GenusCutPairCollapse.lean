module

public import RequestProject.GenusOrdinaryPairCollapse
public import RequestProject.PositiveBoundaryCoordinates

@[expose] public section

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb
variable (q : ℕ) [NeZero q]


/-- Positivity and dimension of a recorded cut pair. -/
theorem genus_cut_pair_data
    (left right : List (GenusCollapsePair q))
    (σ : CutCell (cmpRel (GenusVertex q))) (t : QOld (cmpRel (GenusVertex q)))
    (hsplit : genusChainCollapse q = left ++
      ((qCubeToCoordinate t.1, Sum.inr σ.1) :: right)) :
    t.1.spx = σ.1 ∧ t.1.spx.Nonempty ∧ t.1.spx.card = 3 ∧ t.1.sgn = 0 := by
  classical
  have d := genus_pair_data q (s := Sum.inr σ) hsplit
  have he : qCubeToCoordinate t.1 = posCube σ.1 := by
    have hi := d.incident
    change qCubeToCoordinate t.1 ∈ spineInc (ASC.orderComplex (GenusVertex q)) (Sum.inr σ.1) at hi
    simp only [spineInc] at hi
    split at hi
    · exact Finset.mem_singleton.mp hi
    · simp at hi
  have hs : t.1.spx = σ.1 := by
    have hh := congrArg freeSet he
    simpa using hh
  have hpositive : t.1.sgn = 0 := by
    funext v
    have hh := qCubeToCoordinate_parity t.1 v
    rw [he] at hh
    by_cases hv : v ∈ σ.1 <;> simpa [posCube, hv] using hh.symm
  have hne  := hs.symm ▸ σ.2.1
  exact ⟨hs, hne, d.dim_top, hpositive⟩

end FiniteChains.Davis.Genus
