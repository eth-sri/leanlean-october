/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.AffineSubdivisionGeometry


/-! # Barycentric subdivision strictly decreases mesh

Every vertex tuple in the support has the proved smaller diameter bound.
The estimate includes cancellations, repeated vertices and degree zero.
-/

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

def MeshBound {n : ℕ} (v : Vertices A n) (D : ℝ) :=
  ∀ i j, dist (v i).val (v j).val ≤ D

noncomputable def meshChains (n : ℕ) (D : ℝ) : Submodule ℤ (VertexChains.Chain A n) :=
  Finsupp.supported ℤ ℤ {v | MeshBound v D}

theorem shrink_le_succ n : shrink n ≤ shrink (n + 1) := by
  simp [shrink, Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem subdivide_single_mem_mesh n v D (hD₀ : 0 ≤ D)
    (hD : MeshBound v D) :
    subdivide (center hA) n (Finsupp.single v 1) ∈ meshChains n (shrink n * D) := by
  induction n generalizing D with
  | zero =>
    refine Finsupp.single_mem_supported ℤ 1 ?_
    intro i j
    have hij : i = j := by omega
    rw [hij, dist_self]
    simp [shrink]
  | succ n ih =>
    rw [subdivide_succ_single, one_smul, VertexChains.boundary_single]
    simp only [map_sum, map_zsmul]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply map_mem_of_supported
      {w : Vertices A n | (∀ j, (w j).val ∈ convexHull ℝ (Set.range (fun j => (v j).val))) ∧
        MeshBound w (shrink n * D)} _ (cone (center hA _ v) n) ?_ ?_
    · intro w hw
      rw [cone_single]
      refine Finsupp.single_mem_supported ℤ 1 ?_
      intro a b
      refine Fin.cases ?_ (fun a => ?_) a
      · refine Fin.cases ?_ (fun b => ?_) b
        · simpa [dist_self] using mul_nonneg (shrink_nonneg _) hD₀
        · exact center_dist_convexHull_le hA v D hD (hw.1 b)
      · refine Fin.cases ?_ (fun b => ?_) b
        · rw [dist_comm]
          exact center_dist_convexHull_le hA v D hD (hw.1 a)
        · exact (hw.2 a b).trans (mul_le_mul_of_nonneg_right (shrink_le_succ n) hD₀)
    · intro w hw
      refine ⟨?_, (ih _ D hD₀ (by tauto)) hw⟩
      intro j
      apply convexHull_mono ?_ (subdivide_vertices_mem_convexHull hA _ hw j)
      rintro x ⟨k, rfl⟩
      exact ⟨i.succAbove k, rfl⟩

theorem subdivide_mem_mesh n D (hD₀ : 0 ≤ D) {c}
    (hc : c ∈ meshChains n D) : subdivide (center hA) n c ∈ meshChains n (shrink n * D) :=
  map_mem_of_supported _ _ _
    (subdivide_single_mem_mesh hA n · D hD₀ ·) hc

theorem iterated_subdivide_mem_mesh k n D (hD₀ : 0 ≤ D) {c}
    (hc : c ∈ meshChains n D) :
    ((subdivide (center hA) n)^[k]) c ∈ meshChains n ((shrink n) ^ k * D) := by
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have he := subdivide_mem_mesh hA n _
      (mul_nonneg (pow_nonneg (shrink_nonneg n) k) hD₀) ih
    grind
