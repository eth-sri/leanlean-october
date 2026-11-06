/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.VertexSubdivision
import RequestProject.TopologicalSingular.SingularChainMaps
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Basic
import RequestProject.Tac
noncomputable section


/-! # Realization of vertex chains as affine singular simplices

All vertices lie in an actual convex subspace of a real normed space.
The realization is continuous, respects every face, and carries the
formal boundary to the actual singular boundary. The chosen centers are
the genuine equally weighted barycenters.
-/


bwd

namespace FiniteChains.AffineVertexChains

open Set Topology VertexChains

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {A : Set E} {B : Set F} (hA : Convex ℝ A) (hB : Convex ℝ B)

def affineEval {n : ℕ} (v : Vertices A n) : TopologicalSingular.Simplex A n :=
  ⟨fun z => ⟨∑ i, z.val i • (v i).val,
    hA.sum_mem (fun i _ => z.property.1 i) z.property.2 (by simp)⟩, by
    apply Continuous.subtype_mk
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const⟩

theorem affineEval_apply v (z : TopologicalSingular.Domain n) :
    (affineEval hA v z).val = ∑ i, z.val i • (v i).val := rfl

theorem affineEval_reindex (f : Fin (m + 1) → Fin (n + 1))
    (v : Vertices A n) z :
    affineEval hA (v ∘ f) z = affineEval hA v (stdSimplex.map f z) := by
  classical
  apply Subtype.ext
  change (∑ i, z.val i • (v (f i)).val) = ∑ j, (stdSimplex.map f z).val j • (v j).val
  symm
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ.filter (f · = j), z.val i • (v (f i)).val := by
      apply Finset.sum_congr rfl
      intro j _
      change (FunOnFinite.linearMap ℝ ℝ f z.val) j • (v j).val = _
      rw [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
      apply Finset.sum_congr rfl
      simp_all
    _ = _ := Finset.sum_fiberwise Finset.univ f _

theorem face_affineEval i (v : Vertices A (n + 1)) :
    TopologicalSingular.face i (affineEval hA v) = affineEval hA (face i v) := by
  apply ContinuousMap.ext
  intro z
  exact (affineEval_reindex hA i.succAbove v z).symm

def realize (n : ℕ) : VertexChains.Chain A n →ₗ[ℤ] TopologicalSingular.Chain A n :=
  Finsupp.lmapDomain ℤ ℤ (affineEval hA)

@[simp] theorem realize_single n v r :
    realize hA n (Finsupp.single v r) = Finsupp.single (affineEval hA v) r :=
  Finsupp.mapDomain_single

theorem realize_boundary n c :
    realize hA n (VertexChains.boundary n c) = TopologicalSingular.boundary n (realize hA (n + 1) c) := by
  have he : (realize hA n).comp (VertexChains.boundary n) =
      (TopologicalSingular.boundary n).comp (realize hA _) := by
    apply Finsupp.lhom_ext
    grind [LinearMap.comp_apply, VertexChains.boundary_single, realize_single, TopologicalSingular.boundary_single, map_sum, map_zsmul, face_affineEval]
  exact DFunLike.congr_fun he c

def center (n : ℕ) (v : Vertices A n) := affineEval hA v stdSimplex.barycenter

theorem center_val n v :
    (center hA n v).val = ∑ i, ((n + 1 : ℕ) : ℝ)⁻¹ • (v i).val := by
  simp [center, affineEval_apply, stdSimplex.barycenter_apply, Fintype.card_fin]

def restriction (f : E →L[ℝ] F) (hf : MapsTo f A B) : C(A, B) :=
  ⟨fun a => ⟨f a.val, hf a.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem affineEval_naturality f hf {n} v :
    TopologicalSingular.simplexMap (restriction f hf) n (affineEval hA v) =
      affineEval hB (restriction f hf ∘ v) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change f (∑ i, z.val i • (v i).val) = ∑ i, z.val i • f (v i).val
  simp

theorem center_naturality (f : E →L[ℝ] F) hf n v :
    restriction f hf (center hA n v) = center hB n (restriction f hf ∘ v) :=
  DFunLike.congr_fun (affineEval_naturality hA hB f hf v) stdSimplex.barycenter

theorem realize_naturality (f : E →L[ℝ] F) hf n
    c :
    TopologicalSingular.map (restriction f hf) n (realize hA n c) =
      realize hB n (VertexChains.map (restriction f hf) n c) := by
  have he : (TopologicalSingular.map (restriction f hf) n).comp (realize hA n) =
      (realize hB n).comp (VertexChains.map (restriction f hf) n) := by
    apply Finsupp.lhom_ext
    simp [LinearMap.comp_apply, realize_single, TopologicalSingular.map_single, VertexChains.map_single, affineEval_naturality hA hB f hf]
  exact DFunLike.congr_fun he c

def standardVertices d : Vertices (TopologicalSingular.Domain d) d :=
  stdSimplex.vertex

theorem affineEval_standardVertices d :
    affineEval (convex_stdSimplex ℝ (Fin (d + 1))) (standardVertices d) =
      ContinuousMap.id (TopologicalSingular.Domain d) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  funext j
  simp [affineEval, standardVertices, Finset.sum_apply, Pi.single_apply]
