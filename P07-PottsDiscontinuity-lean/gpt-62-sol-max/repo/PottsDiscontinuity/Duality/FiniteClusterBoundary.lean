module

public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.LatticeCellBoundaryParity
public import PottsDiscontinuity.Duality.WholePlaneDualConfiguration

/-! The dual boundary of a finite union of open clusters. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial
noncomputable section

/-- Cell bases representing primal vertices, with the dual face-base convention. -/
def vertexCellBases (C : Finset LatticeVertex) : Finset LatticeVertex :=
  C.image fun v => (v.1 - 1, v.2 - 1)

lemma mem_vertexCellBases (C : Finset LatticeVertex) (x : LatticeVertex) :
    x ∈ vertexCellBases C ↔ (x.1 + 1, x.2 + 1) ∈ C := by
  constructor
  · rintro hx
    obtain ⟨v, hv, h⟩ := Finset.mem_image.1 hx
    grind
  · intro hx
    apply Finset.mem_image.2
    grind

/-- The literal cell boundary of a finite actual cluster consists of closed-dual edges. -/
theorem clusterCellBoundary_le_dualOpen (ω : LatticeConfiguration)
    (C : Finset LatticeVertex) (hC : ∀ ⦃u v⦄, (rcInfiniteOpenGraph ω).Adj u v → (u ∈ C ↔ v ∈ C)) :
    latticeCellBoundaryGraph (vertexCellBases C) ≤ rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω) := by
  intro x y hxy
  obtain ⟨_, d, hd, hfaces⟩ := (latticeCellBoundaryGraph_adj_iff _ x y).1 hxy
  have hsource : ((d.faceBase false).1 + 1, (d.faceBase false).2 + 1) =
      (primalBondOfDual d).source := by
    grind [LatticeBond.faceBase, primalBondOfDual, LatticeBond.source]
  have htarget : ((d.faceBase true).1 + 1, (d.faceBase true).2 + 1) =
      (primalBondOfDual d).target := by
    rcases d with ⟨⟨a, b⟩, ax⟩
    cases ax <;> rfl
  have hdopen : (rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω)).Adj d.source d.target := by
    rw [rcInfiniteOpenGraph_adj_bond, wholePlaneDualConfigurationHomeomorph_bondState, Bool.not_eq_true']
    by_contra h
    have hi := hC ((rcInfiniteOpenGraph_adj_bond ω (primalBondOfDual d)).2 (by simpa using h))
    rw [mem_vertexCellBases, mem_vertexCellBases, htarget, hsource] at hfaces
    simp_all
  change s(d.source, d.target) = s(x, y) at hd
  rcases Sym2.eq_iff.1 hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hdopen
  · exact hdopen.symm

end
end PottsDiscontinuity.Duality
