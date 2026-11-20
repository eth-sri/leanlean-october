module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.RelativeSingularChains

@[expose] public section

/-! # Functorial relative singular chains for maps of topological pairs -/

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u
variable {X : Type u} [TopologicalSpace X] (A : Set X) (n : ℕ)

/-- The range of subspace chains is the support condition on simplices. -/
theorem subChains_eq_supported :
    subChains A n = Finsupp.supported ℤ ℤ {σ : Simplex X n | ∀ z, σ z ∈ A} := by
  have h : Set.range (simplexMap (inclusion A) n) = {σ | ∀ z, σ z ∈ A} := by
    ext σ
    exact ⟨fun ⟨τ, e⟩ z => e ▸ (τ z).2, fun hσ => ⟨⟨fun z => ⟨σ z, hσ z⟩, σ.continuous.subtype_mk _⟩, rfl⟩⟩
  simpa [subChains, map, h] using Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ)
    (simplexMap (inclusion A) n) Set.univ

theorem single_mem_subChains (σ : Simplex X n) (r : ℤ)
    (hσ : ∀ z, σ z ∈ A) : Finsupp.single σ r ∈ subChains A n := by
  rw [subChains_eq_supported]
  exact Finsupp.single_mem_supported ℤ r hσ

end FiniteChains.TopologicalSingular
