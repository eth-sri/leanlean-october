import Mathlib.Tactic

import RequestProject.TopologicalSingular.SmallChainHomology
import RequestProject.TopologicalSingular.RelativeSingularMaps

namespace FiniteChains.TopologicalSingular
variable {X : Type u} [TopologicalSpace X]

/-- Subspace chains are precisely chains whose basis simplices stay in the subspace. -/
theorem subChains_eq_supported (A : Set X) (n : ℕ) :
    subChains A n = Finsupp.supported ℤ ℤ {σ : Simplex X n | ∀ z, σ z ∈ A} := by
  apply le_antisymm
  · rintro c ⟨b, rfl⟩
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b c hb hc => aesop
    | single σ r =>
      rw [map_single]
      exact Finsupp.single_mem_supported ℤ r (fun z => (σ z).property)
  · intro c hc
    have he := VertexChains.map_mem_of_supported
      {σ : Simplex X n | ∀ z, σ z ∈ A} (subChains A n) (LinearMap.id : Chain X n →ₗ[ℤ] _) 
      (fun σ hσ => single_mem_subChains A n σ 1 hσ) hc
    exact he

abbrev single_mem_range_subChains {n : ℕ} (σ : Simplex X n) (r : ℤ)  :=
  FiniteChains.TopologicalSingular.single_mem_subChains (Set.range ⇑σ) n σ r
    fun (z : ↑(FiniteChains.TopologicalSingular.Domain n)) => Exists.intro z rfl

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
variable {X : Type u} [TopologicalSpace X]

  (A : Set X)
theorem fromModel_mem_subChains  {k l : ℕ} (m : Chain (Domain k) l)
    {c : Chain X k} (hc : c ∈ subChains A k) : fromModel m c ∈ subChains A l := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨fromModel m b, fromModel_naturality m (inclusion A) b⟩

theorem iterated_subdivide_mem_subChains  (k n : ℕ)
    {c : Chain X n} (hc : c ∈ subChains A n) :
    ((subdivide n)^[k]) c ∈ subChains A n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact fromModel_mem_subChains A (model n) ih

theorem iteratedHomotopy_mem_subChains  (k n : ℕ)
    {c : Chain X n} (hc : c ∈ subChains A n) :
    iteratedHomotopy n k c ∈ subChains A (n + 1) := by
  induction k with
  | zero => simp_all [iteratedHomotopy_zero]
  | succ k ih =>
    rw [iteratedHomotopy_succ]
    exact Submodule.add_mem _
      (fromModel_mem_subChains A (homotopyModel n) (iterated_subdivide_mem_subChains A k n hc)) ih

end FiniteChains.SingularSubdivision
