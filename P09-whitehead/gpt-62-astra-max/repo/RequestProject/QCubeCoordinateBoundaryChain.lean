module

public import RequestProject.QCubeCoordinateFacetRecovery
public import RequestProject.QCubeFacetIndex

@[expose] public section

/-! Finite coordinate facet chains realize the collapse's ordinary cubical boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

variable (c : QCube A)

noncomputable def qCubeCoordinateFacetChain :=
  ∑ i : {v : V // v ∈ c.spx} × ZMod 2,
    Finsupp.single (qCubeToCoordinate (qCubeFacetIndex c i))
      (incid (qCubeToCoordinate (qCubeFacetIndex c i)) i.1.1)

/-- Every coefficient of the genuine finite coordinate facet chain is the ordinary
cubical boundary coefficient used by the truncated collapse. -/
theorem qCubeCoordinateFacetChain_apply (g : Cube V) :
    qCubeCoordinateFacetChain c g = cubeBdry (qCubeToCoordinate c) (Sum.inl g) := by
  classical
  simp only [qCubeCoordinateFacetChain, Finsupp.finset_sum_apply]
  by_cases hg : ∃ i : {v : V // v ∈ c.spx} × ZMod 2,
      qCubeToCoordinate (qCubeFacetIndex c i) = g
  · obtain ⟨i, rfl⟩ := hg
    rw [Finset.sum_eq_single i]
    · simp only [Finsupp.single_eq_same]
      exact (cubeBdry_actual_facet c _ i.1.2 i.2).symm
    · intro j _ hji
      have hne : qCubeToCoordinate (qCubeFacetIndex c j) ≠
          qCubeToCoordinate (qCubeFacetIndex c i) := fun h => hji ((qCubeToCoordinate_injective.comp (qCubeFacetIndex_injective c)) h)
      simp [hne]
    · simp
  · have hzero : cubeBdry (qCubeToCoordinate c) (Sum.inl g) = 0 := by
      apply cubeBdry_zero_off_actual_facets
      intro v hv s he
      exact hg ⟨(⟨v, hv⟩, s), he.symm⟩
    rw [hzero]
    apply Finset.sum_eq_zero <;> grind

end FiniteChains.Davis
