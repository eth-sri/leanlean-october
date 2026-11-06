import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.RelativeSingularChains

/-! # Functorial relative singular chains for maps of topological pairs -/



namespace FiniteChains.TopologicalSingular



variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem single_mem_subChains (A : Set X) (n : ℕ) (σ : Simplex X n) (r : ℤ)
    (hσ : ∀ z, σ z ∈ A) : Finsupp.single σ r ∈ subChains A n := by
  let τ : Simplex A n := ⟨fun z => ⟨σ z, hσ z⟩, σ.continuous.subtype_mk _⟩
  refine ⟨Finsupp.single τ r, ?_⟩
  rw [map_single]
  rfl

end FiniteChains.TopologicalSingular
