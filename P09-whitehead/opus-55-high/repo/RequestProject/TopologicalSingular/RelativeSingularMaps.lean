/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.RelativeSingularChains
import RequestProject.Tac


/-! # Functorial relative singular chains for maps of topological pairs -/

bwd

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem single_mem_subChains A n (σ : Simplex X n) r
    (hσ : ∀ z, σ z ∈ A) : Finsupp.single σ r ∈ subChains A n := by
  let τ : Simplex A n := ⟨fun z => ⟨σ z, hσ z⟩, σ.continuous.subtype_mk _⟩
  refine ⟨Finsupp.single τ r, ?_⟩
  aesop
