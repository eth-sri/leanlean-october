import RequestProject.TopologicalSingular.SmallChainHomology
import RequestProject.TopologicalSingular.RelativeSingularMaps
import RequestProject.Tac


namespace FiniteChains.TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

/-- Subspace chains are precisely chains whose basis simplices stay in the subspace. -/
theorem subChains_eq_supported A n :
    subChains A n = Finsupp.supported ℤ ℤ {σ : Simplex X n | ∀ z, σ z ∈ A} := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    lin_ind b σ r using aesop =>
      rw [map_single]
      exact Finsupp.single_mem_supported ℤ r (fun z => (σ z).property)
  · intro c hc
    have he := VertexChains.map_mem_of_supported
      _ _ (LinearMap.id : Chain X n →ₗ[ℤ] _) 
      (fun σ hσ => single_mem_subChains A n σ 1 hσ) hc
    exact he

theorem single_mem_range_subChains (σ : Simplex X n) r :
    Finsupp.single σ r ∈ subChains (Set.range σ) n :=
  single_mem_subChains _ _ _ _ (by simp)

/-- A map carried by each basis simplex preserves every subspace chain module. -/
theorem carried_linearMap_mem_subChains (f : Chain X n →ₗ[ℤ] Chain X k)
    (hf : ∀ σ : Simplex X n, f (Finsupp.single σ 1) ∈ subChains (Set.range σ) k)
    A {c} (hc : c ∈ subChains A n) : f c ∈ subChains A k := by
  rw [subChains_eq_supported] at hc
  apply VertexChains.map_mem_of_supported _ _ f ?_ hc
  intro σ hσ
  exact subChains_mono (by grind) k (hf σ)

end FiniteChains.TopologicalSingular

namespace FiniteChains.SingularSubdivision
open TopologicalSingular
universe u
variable {X : Type u} [TopologicalSpace X]

theorem fromModel_mem_subChains A {k l} m
    {c : Chain X k} (hc : c ∈ subChains A k) : fromModel m c ∈ subChains A l := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨fromModel m b, fromModel_naturality m _ b⟩

theorem iterated_subdivide_mem_subChains A k n
    {c : Chain X n} (hc : c ∈ subChains A n) :
    ((subdivide n)^[k]) c ∈ subChains A n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fromModel_mem_subChains A _ ih

theorem iteratedHomotopy_mem_subChains A k n
    {c : Chain X n} (hc : c ∈ subChains A n) :
    iteratedHomotopy n k c ∈ subChains A (n + 1) := by
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    rw [iteratedHomotopy_succ]
    exact Submodule.add_mem _
      (fromModel_mem_subChains A _ (iterated_subdivide_mem_subChains A k n hc)) ih
