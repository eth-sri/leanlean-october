module

public import RequestProject.OrderNerveRealizationStarContractible
public import RequestProject.TopologicalSingular.SingularChains

@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

variable {P : Type} [PartialOrder P]

/-- The vertices with positive coordinates at a realization point form a
finite chain. This remains true in an infinite, non-locally-finite realization. -/
theorem orderNerveRealization_activeVertices_finite_chain
    (x : orderNerveRealization P) :
    {v | x ∈ orderNerveRealizationOpenStar P v}.Finite ∧
      IsChain (· ≤ ·) {v | x ∈ orderNerveRealizationOpenStar P v} := by
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  have hs : {v | x ∈ orderNerveRealizationOpenStar P v} = Set.range s.val.obj := by
    ext v
    rw [← he]
    apply orderNerveRealizationSimplex_mem_openStar_iff <;> assumption
  rw [hs]
  refine ⟨Set.finite_range s.val.obj, ?_⟩
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ _
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

variable {n : ℕ}

variable (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)

/-- All open vertex stars that contain the entire singular simplex. -/
def orderNerveSingularStarIndices :=
  {v | ∀ z, σ z ∈ orderNerveRealizationOpenStar P v}

theorem orderNerveSingularStarIndices_chain :
    IsChain (· ≤ ·) (orderNerveSingularStarIndices σ) :=
  (orderNerveRealization_activeVertices_finite_chain (σ _)).2.mono
    (fun _ h => h (stdSimplex.vertex 0))

/-- The common closed-star subposet of every star containing a singular simplex.
Taking all such stars makes this carrier monotone under passage to faces. -/
def orderNerveSingularCarrier
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :=
  {p | ∀ v ∈ orderNerveSingularStarIndices σ, p ≤ v ∨ v ≤ p}

theorem orderNerveSingularCarrier_face
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) _)
    (i : Fin (n + 2)) :
    orderNerveSingularCarrier (TopologicalSingular.face i σ) ⊆ orderNerveSingularCarrier σ := by
  intro p hp v hv
  solve_by_elim

variable (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)

theorem orderNerveSingularStarIndices_subset_carrier :
    orderNerveSingularStarIndices σ ⊆ orderNerveSingularCarrier σ := by
  intro p hp v hv
  exact (orderNerveSingularStarIndices_chain σ).total hp hv

/-- The whole singular simplex lies in its genuine supported CW carrier. -/
theorem orderNerveSingularSimplex_mem_carrier
    (z : TopologicalSingular.Domain n) :
    σ z ∈ (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
      Set _) := by
  intro p hp
  by_contra he
  apply hp
  intro v hv
  by_contra hcomp
  solve_by_elim [orderNerveRealizationOpenStar_subset_subcomplex]

variable (hσ : (orderNerveSingularStarIndices σ).Nonempty)
include hσ

/-- The carrier of a star-small simplex has a universally comparable vertex,
so its order realization is contractible. -/
theorem orderNerveSingularCarrier_realization_contractible :
    ContractibleSpace (orderNerveRealization (orderNerveSingularCarrier σ)) := by
  obtain ⟨v, hv⟩ := hσ
  exact orderNerveRealization_contractible_of_comparable (⟨v, orderNerveSingularStarIndices_subset_carrier σ hv⟩) (fun p => p.property v hv)

theorem orderNerveSingularCarrier_subcomplex_contractible :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
      Set (orderNerveRealization P)) := by
  letI := orderNerveSingularCarrier_realization_contractible σ hσ
  exact (orderNerveRealizationSubtypeHomeomorph (orderNerveSingularCarrier σ)).symm.contractibleSpace

end FiniteChains.Comb
