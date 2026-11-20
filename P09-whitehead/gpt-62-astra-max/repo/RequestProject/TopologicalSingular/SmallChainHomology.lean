module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SmallSingularChains

@[expose] public section

/-! # Small representatives and small fillings of singular cycles

For an open cover, every cycle is homologous to a small cycle. A small
cycle bounding in the ambient singular complex already bounds by a small
chain. The accumulated subdivision homotopy is explicit.
-/

namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v}

variable (k n : ℕ)

theorem iterated_subdivide_zero : ((subdivide (X := X) n)^[k]) 0 = 0 := by
  simp

theorem iterated_subdivide_boundary (c : Chain X _) :
    ((subdivide n)^[k]) (boundary n c) = boundary n (((subdivide (n + 1))^[k]) c) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Function.iterate_succ_apply', ih, subdivide_boundary]

noncomputable def iteratedHomotopy (n : ℕ) : ℕ → Chain X n →ₗ[ℤ] Chain X (n + 1)
  | 0 => 0
  | k + 1 => (homotopy n).comp ((subdivide n) ^ k) + iteratedHomotopy n k

theorem iteratedHomotopy_zero (n : ℕ) (c : Chain X n) : iteratedHomotopy n 0 c = 0 := rfl

theorem iteratedHomotopy_succ (n k : ℕ) (c : Chain X n) :
    iteratedHomotopy n (k + 1) c = homotopy n (((subdivide n)^[k]) c) + iteratedHomotopy n k c := by
  simp [iteratedHomotopy, LinearMap.add_apply, LinearMap.comp_apply, Module.End.pow_apply]

theorem iteratedHomotopy_identity_succ (k n : ℕ) (c : Chain X _) :
    boundary _ (iteratedHomotopy _ k c) + iteratedHomotopy n k (boundary n c) =
      ((subdivide (n + 1))^[k]) c - c := by
  induction k with
  | zero => simp_all [iteratedHomotopy_zero]
  | succ k ih =>
    rw [iteratedHomotopy_succ, iteratedHomotopy_succ, map_add, iterated_subdivide_boundary]
    rw [Function.iterate_succ_apply']
    linear_combination (norm := abel) homotopy_identity_succ n (((subdivide (n + 1))^[k]) c) + ih

theorem iteratedHomotopy_mem_small (U : ι → Set X) (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : iteratedHomotopy n k c ∈ smallChains U _ := by
  induction k with
  | zero => apply Submodule.zero_mem
  | succ k ih =>
    rw [iteratedHomotopy_succ]
    exact Submodule.add_mem _ (homotopy_mem_small U n (iterated_subdivide_mem_small U k n hc)) ih

variable (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)

include hU hcover in
theorem exists_small_cycle_representative (n : ℕ) (c : Chain X _) (hc : boundary n c = 0) :
    ∃ d : Chain X _, d ∈ smallChains U _ ∧ boundary n d = 0 ∧
      d - c ∈ LinearMap.range (boundary _) := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover _ c
  refine ⟨_, hk, ?_, iteratedHomotopy _ k c, ?_⟩
  · rw [← iterated_subdivide_boundary, hc, iterated_subdivide_zero]
  · simpa only [hc, map_zero, add_zero] using iteratedHomotopy_identity_succ k n c

end FiniteChains.SingularSubdivision
