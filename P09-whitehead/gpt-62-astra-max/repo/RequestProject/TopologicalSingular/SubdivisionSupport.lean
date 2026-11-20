module

public import RequestProject.TopologicalSingular.SmallChainHomology
public import RequestProject.TopologicalSingular.RelativeSingularMaps

@[expose] public section

namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

theorem single_mem_range_subChains {n : ℕ} (σ : Simplex X n) (r : ℤ) :
    Finsupp.single σ r ∈ subChains (Set.range σ) n :=
  by solve_by_elim [single_mem_subChains]

/-- A map carried by each basis simplex preserves every subspace chain module. -/
theorem carried_linearMap_mem_subChains {n k : ℕ} (f : Chain X n →ₗ[ℤ] Chain X k)
    (hf : ∀ σ : Simplex X n, f (Finsupp.single σ 1) ∈ subChains (Set.range σ) k)
    (A : Set X) {c : Chain X n} (hc : c ∈ subChains A n) : f c ∈ subChains A k := by
  rw [subChains_eq_supported] at hc
  apply VertexChains.map_mem_of_supported _ _ f ?_ hc
  intro σ hσ
  exact subChains_mono (by rintro _ ⟨z, rfl⟩; exact hσ z) k (hf σ)

end FiniteChains.TopologicalSingular

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

/-- A singleton family imposes exactly the subspace support condition. -/
theorem smallChains_const (A : Set X) (n : ℕ) :
    smallChains (fun _ : Unit => A) n = subChains A n := by
  simp [smallChains, subChains_eq_supported]

end FiniteChains.SingularSubdivision
