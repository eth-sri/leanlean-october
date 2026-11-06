import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SmallSingularChains

/-! # Small representatives and small fillings of singular cycles

For an open cover, every cycle is homologous to a small cycle. A small
cycle bounding in the ambient singular complex already bounds by a small
chain. The accumulated subdivision homotopy is explicit.
-/

namespace FiniteChains.SingularSubdivision

open Set Topology TopologicalSingular

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

  (k n : ℕ)
theorem iterated_subdivide_zero  : ((subdivide (X := X) n)^[k]) 0 = 0 := by
  rw [← Module.End.pow_apply, map_zero]

theorem iterated_subdivide_boundary  (c : Chain X (n + 1)) :
    ((subdivide n)^[k]) (boundary n c) = boundary n (((subdivide (n + 1))^[k]) c) := by
  induction k <;> simp_all [Function.iterate_succ_apply', subdivide_boundary]

noncomputable def iteratedHomotopy (n : ℕ) : ℕ → Chain X n →ₗ[ℤ] Chain X (n + 1)
  | 0 => 0
  | k + 1 => (homotopy n).comp ((subdivide n) ^ k) + iteratedHomotopy n k

theorem iteratedHomotopy_zero (n : ℕ) (c : Chain X n) : iteratedHomotopy n 0 c = 0 := rfl

theorem iteratedHomotopy_succ (n k : ℕ) (c : Chain X n) :
    iteratedHomotopy n (k + 1) c = homotopy n (((subdivide n)^[k]) c) + iteratedHomotopy n k c := by simp_all [iteratedHomotopy, Module.End.pow_apply]

theorem iteratedHomotopy_identity_succ  (c : Chain X (n + 1)) :
    boundary (n + 1) (iteratedHomotopy (n + 1) k c) + iteratedHomotopy n k (boundary n c) =
      ((subdivide (n + 1))^[k]) c - c := by
  induction k with
  | zero => classical simp_all [iteratedHomotopy_zero, map_zero, add_zero, sub_self]
  | succ k ih =>
    rw [iteratedHomotopy_succ, iteratedHomotopy_succ, map_add, iterated_subdivide_boundary]
    calc
      _ = (boundary (n + 1) (homotopy (n + 1) (((subdivide (n + 1))^[k]) c)) +
            homotopy n (boundary n (((subdivide (n + 1))^[k]) c))) +
          (boundary (n + 1) (iteratedHomotopy (n + 1) k c) +
            iteratedHomotopy n k (boundary n c)) := by abel
      _ = (subdivide (n + 1) (((subdivide (n + 1))^[k]) c) - ((subdivide (n + 1))^[k]) c) +
          (((subdivide (n + 1))^[k]) c - c) := by rw [homotopy_identity_succ, ih]
      _ = _ := by rw [Function.iterate_succ_apply']; abel

theorem iteratedHomotopy_mem_small (U : ι → Set X) (k n : ℕ) {c : Chain X n}
    (hc : c ∈ smallChains U n) : iteratedHomotopy n k c ∈ smallChains U (n + 1) := by
  induction k with
  | zero => classical simp_all [iteratedHomotopy_zero]
  | succ k ih =>
    aesop (add simp [FiniteChains.SingularSubdivision.iteratedHomotopy_succ, FiniteChains.SingularSubdivision.homotopy_mem_small, FiniteChains.SingularSubdivision.iterated_subdivide_mem_small])

variable (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)

include hU hcover in
theorem exists_small_cycle_representative (n : ℕ) (c : Chain X (n + 1)) (hc : boundary n c = 0) :
    ∃ d : Chain X (n + 1), d ∈ smallChains U (n + 1) ∧ boundary n d = 0 ∧
      d - c ∈ LinearMap.range (boundary (n + 1)) := by
  obtain ⟨k, hk⟩ := exists_subdivision_small U hU hcover (n + 1) c
  refine ⟨_, hk, ?_, iteratedHomotopy (n + 1) k c, ?_⟩
  · rw [← iterated_subdivide_boundary, hc, iterated_subdivide_zero]
  · classical grind [iteratedHomotopy_identity_succ]

end FiniteChains.SingularSubdivision
