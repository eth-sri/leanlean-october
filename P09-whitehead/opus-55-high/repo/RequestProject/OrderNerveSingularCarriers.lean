import RequestProject.OrderNerveRealizationStarContractible
import RequestProject.TopologicalSingular.SingularChains


namespace FiniteChains.Comb
open CategoryTheory Simplicial
open scoped Classical

/-- The vertices with positive coordinates at a realization point form a
finite chain. This remains true in an infinite, non-locally-finite realization. -/
theorem orderNerveRealization_activeVertices_finite_chain {P} [PartialOrder P]
    (x : orderNerveRealization P) :
    {v | x ∈ orderNerveRealizationOpenStar P v}.Finite ∧
      IsChain (· ≤ ·) {v | x ∈ orderNerveRealizationOpenStar P v} := by
  obtain ⟨n, s, z, hz, he⟩ := orderNerveRealization_interior_cover P x
  have hs : {v | x ∈ orderNerveRealizationOpenStar P v} = Set.range s.val.obj := by
    ext v
    rw [← he]
    exact orderNerveRealizationSimplex_mem_openStar_iff s.val z hz v
  rw [hs]
  refine ⟨Set.finite_range s.val.obj, ?_⟩
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ _
  rcases le_total i j with hij | hij
  · exact Or.inl (leOfHom (s.val.map (homOfLE hij)))
  · exact Or.inr (leOfHom (s.val.map (homOfLE hij)))

/-- All open vertex stars that contain the entire singular simplex. -/
def orderNerveSingularStarIndices {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :=
  {v | ∀ z, σ z ∈ orderNerveRealizationOpenStar P v}

theorem orderNerveSingularStarIndices_chain {P} [PartialOrder P] {n : ℕ}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :
    IsChain (· ≤ ·) (orderNerveSingularStarIndices σ) :=
  (orderNerveRealization_activeVertices_finite_chain (σ (stdSimplex.vertex 0))).2.mono
    (by tauto)

/-- Every star containing a simplex also contains each of its faces. -/
theorem orderNerveSingularStarIndices_face {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) (n + 1))
    i :
    orderNerveSingularStarIndices σ ⊆
      orderNerveSingularStarIndices (TopologicalSingular.face i σ) := by
  tauto

/-- The common closed-star subposet of every star containing a singular simplex.
Taking all such stars makes this carrier monotone under passage to faces. -/
def orderNerveSingularCarrier {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :=
  {p | ∀ v ∈ orderNerveSingularStarIndices σ, p ≤ v ∨ v ≤ p}

theorem orderNerveSingularCarrier_face {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) (n + 1))
    i :
    orderNerveSingularCarrier (TopologicalSingular.face i σ) ⊆ orderNerveSingularCarrier σ := by
  intro p hp v hv
  exact hp v (orderNerveSingularStarIndices_face σ i hv)

theorem orderNerveSingularStarIndices_subset_carrier {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n) :
    orderNerveSingularStarIndices σ ⊆ orderNerveSingularCarrier σ := by
  intro p hp v hv
  exact (orderNerveSingularStarIndices_chain σ).total hp hv

/-- The whole singular simplex lies in its genuine supported CW carrier. -/
theorem orderNerveSingularSimplex_mem_carrier {P} [PartialOrder P] {n}
    σ
    (z : TopologicalSingular.Domain n) :
    σ z ∈ (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
      Set (orderNerveRealization P)) := by
  intro p hp
  by_contra he
  apply hp
  intro v hv
  by_contra hcomp
  exact he (orderNerveRealizationOpenStar_subset_subcomplex v (hv z) p hcomp)

/-- The carrier of a star-small simplex has a universally comparable vertex,
so its order realization is contractible. -/
theorem orderNerveSingularCarrier_realization_contractible {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) :
    ContractibleSpace (orderNerveRealization (orderNerveSingularCarrier σ)) := by
  cases' hσ with v hv
  let a : orderNerveSingularCarrier σ :=
    ⟨v, orderNerveSingularStarIndices_subset_carrier σ hv⟩
  exact orderNerveRealization_contractible_of_comparable a (by aesop)

theorem orderNerveSingularCarrier_subcomplex_contractible {P} [PartialOrder P] {n}
    (σ : TopologicalSingular.Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) :
    ContractibleSpace (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
      Set (orderNerveRealization P)) := by
  letI := orderNerveSingularCarrier_realization_contractible σ hσ
  exact (orderNerveRealizationSubtypeHomeomorph _).symm.contractibleSpace
