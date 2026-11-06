/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.AffineVertexChains
import RequestProject.TopologicalSingular.VertexCarriers
import Mathlib.Analysis.Normed.Module.Convex


/-! # Convex carriers and barycenter distance estimates

Subdivision and its chain homotopy stay in the original convex hull.
The barycenter of n+1 vertices is at distance at most n/(n+1) times their
diameter bound from every point of that hull. No excision is assumed.
-/

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A : Set E} (hA : Convex ℝ A)

theorem affineEval_mem_of_vertices (hS : Convex ℝ S) {n}
    v (hv : ∀ i, (v i).val ∈ S) (z : TopologicalSingular.Domain n) :
    (affineEval hA v z).val ∈ S :=
  hS.sum_mem (fun i _ => z.property.1 i) z.property.2 (by simp_all)

theorem center_mem_of_vertices (hS : Convex ℝ S) n
    v (hv : ∀ i, (v i).val ∈ S) : (center hA n v).val ∈ S :=
  affineEval_mem_of_vertices hA hS v hv stdSimplex.barycenter

theorem subdivide_mem_convex_carrier (hS : Convex ℝ S) n
    {c} (hc : c ∈ carried {x | x.val ∈ S} n) :
    subdivide (center hA) n c ∈ carried {x | x.val ∈ S} n :=
  subdivide_mem_carried _ _ (center_mem_of_vertices hA hS) n hc

theorem subdivide_vertices_mem_convexHull v
    {w} (hw : w ∈ (subdivide (center hA) n (Finsupp.single v 1)).support) i :
    (w i).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) := by
  have hc := subdivide_mem_convex_carrier hA (convex_convexHull ℝ _) n
    (single_mem_carried {x : A | x.val ∈ convexHull ℝ (Set.range (fun j => (v j).val))} v 1
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩))
  tauto

noncomputable def shrink (n : ℕ) := (n : ℝ) / (n + 1)

theorem shrink_nonneg n : 0 ≤ shrink n := by unfold shrink; positivity

theorem shrink_lt_one n : shrink n < 1 := by
  unfold shrink
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem center_dist_vertex_le v D
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) j :
    dist (center hA n v).val (v j).val ≤ shrink n * D := by
  classical
  let a : ℝ := (n + 1 : ℕ)⁻¹
  have ha : 0 ≤ a := by positivity
  have hsum : ∑ i : Fin (n + 1), a = 1 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, a]
    grind
  have hv : (center hA n v).val - (v j).val = ∑ i, a • ((v i).val - (v j).val) := by
    rw [center_val]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
    rfl
  have hd : (∑ i : Fin (n + 1), dist (v i).val (v j).val) ≤ n * D := by
    calc
      _ = ∑ i ∈ Finset.univ.erase j, dist (v i).val (v j).val := by
        simp
      _ ≤ ∑ _i ∈ Finset.univ.erase j, D := Finset.sum_le_sum (by simp_all)
      _ = _ := by simp
  rw [dist_eq_norm, hv]
  calc
    _ ≤ ∑ i, ‖a • ((v i).val - (v j).val)‖ := norm_sum_le _ _
    _ = a * ∑ i, dist (v i).val (v j).val := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, ← dist_eq_norm, Finset.mul_sum]
    _ ≤ a * (n * D) := mul_le_mul_of_nonneg_left hd ha
    _ = shrink n * D := by simp [a, shrink, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]; ring

theorem center_dist_convexHull_le v D
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) {x}
    (hx : x ∈ convexHull ℝ (Set.range (fun j => (v j).val))) :
    dist (center hA n v).val x ≤ shrink n * D := by
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx _
  rw [dist_comm] at hj
  exact hj.trans (by simpa [dist_comm] using center_dist_vertex_le hA v D hD j)

theorem affineEval_dist_le v D
    (hD : ∀ i j, dist (v i).val (v j).val ≤ D) (z w : TopologicalSingular.Domain n) :
    dist (affineEval hA v z).val (affineEval hA v w).val ≤ D := by
  have hm (t : TopologicalSingular.Domain n) :=
    affineEval_mem_of_vertices hA (convex_convexHull ℝ (Set.range (fun j => (v j).val))) v
      (fun j => subset_convexHull ℝ _ ⟨j, rfl⟩) t
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hij⟩ := convexHull_exists_dist_ge2 (hm z) (hm w)
  grind
