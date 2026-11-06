import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularChainMaps
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Relative singular chains of an actual topological pair

These are quotients by chains of the subspace, not an assumed cellular
chain complex. The short exact sequence and the relative differential
are constructed directly. No excision or homotopy comparison is assumed.
-/

namespace FiniteChains.TopologicalSingular




variable {X : Type u} [TopologicalSpace X]

  (A : Set X)
def inclusion  : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩

variable (n : ℕ)
theorem simplexMap_inclusion_injective   :
    Function.Injective (simplexMap (inclusion A) n) := by
  intro σ τ he
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact DFunLike.congr_fun he z

theorem map_inclusion_injective   : Function.Injective (map (inclusion A) n) := Finsupp.mapDomain_injective (simplexMap_inclusion_injective A n)

noncomputable def subChains   : Submodule ℤ (Chain X n) :=
  LinearMap.range (map (inclusion A) n)

theorem boundary_mem_subChains   {c : Chain X (n + 1)}
    (hc : c ∈ subChains A (n + 1)) : boundary n c ∈ subChains A n := by
  obtain ⟨b, rfl⟩ := hc
  exact ⟨boundary n b, map_boundary (inclusion A) n b⟩

theorem subChains_mono {A B : Set X} (h : A ⊆ B) (n : ℕ) : subChains A n ≤ subChains B n := by
  let j : C(A, B) := ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩
  rintro _ ⟨c, rfl⟩
  refine ⟨map j n c, ?_⟩
  have he : (inclusion B).comp j = inclusion A := rfl
  have hm := DFunLike.congr_fun (map_comp j (inclusion B) n) c
  rw [he] at hm
  exact hm.symm

end FiniteChains.TopologicalSingular
