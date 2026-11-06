/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularSubdivisionModels
import RequestProject.Tac
noncomputable section


/-! # Barycentric subdivision of actual singular chains

The universal affine chains are pushed forward by each continuous
singular simplex. The operator commutes with boundary and is naturally
chain homotopic to the identity. No mesh or excision conclusion is assumed.
-/

bwd

namespace FiniteChains.SingularSubdivision

open TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

def fromModel (m : Chain (Domain k) l) : Chain X k →ₗ[ℤ] Chain X l :=
  Finsupp.linearCombination ℤ (fun σ : Simplex X k => TopologicalSingular.map σ l m)

theorem fromModel_single m (σ : Simplex X k) r :
    fromModel m (Finsupp.single σ r) = r • TopologicalSingular.map σ l m :=
  Finsupp.linearCombination_single ℤ r σ

theorem fromModel_naturality m (f : C(X, Y)) (c : Chain X k) :
    TopologicalSingular.map f l (fromModel m c) = fromModel m (TopologicalSingular.map f k c) := by
  have he : (TopologicalSingular.map f l).comp (fromModel m) =
      (fromModel m).comp (TopologicalSingular.map f k) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp [LinearMap.comp_apply, fromModel_single, one_smul, map_single]
    exact (DFunLike.congr_fun (map_comp σ f l) m).symm
  exact DFunLike.congr_fun he c

def subdivide n : Chain X n →ₗ[ℤ] Chain X n := fromModel (model n)

def homotopy n : Chain X n →ₗ[ℤ] Chain X (n + 1) := fromModel (homotopyModel n)

theorem subdivide_single n (σ : Simplex X n) r :
    subdivide n (Finsupp.single σ r) = r • TopologicalSingular.map σ n (model n) := fromModel_single _ _ _

theorem homotopy_single n (σ : Simplex X n) r :
    homotopy n (Finsupp.single σ r) = r • TopologicalSingular.map σ (n + 1) (homotopyModel n) :=
  fromModel_single _ _ _

theorem push_face (σ : Simplex X (n + 1)) i c :
    TopologicalSingular.map σ k (TopologicalSingular.map (standardMap i.succAbove) k c) =
      TopologicalSingular.map (face i σ) k c :=
  (DFunLike.congr_fun (map_comp _ σ k) c).symm

theorem subdivide_boundary n (c : Chain X (n + 1)) :
    subdivide n (boundary n c) = boundary n (subdivide (n + 1) c) := by
  have he : (subdivide n).comp (boundary n) = (boundary n).comp (subdivide (X := X) _) := by
    apply VertexChains.linearMap_ext_basis
    simp [LinearMap.comp_apply, boundary_single, map_sum, map_zsmul, subdivide_single, one_smul, ← map_boundary, boundary_model, push_face]
  exact DFunLike.congr_fun he c

theorem homotopy_identity_succ n (c : Chain X (n + 1)) :
    boundary (n + 1) (homotopy (n + 1) c) + homotopy n (boundary n c) = subdivide (n + 1) c - c := by
  have he : (boundary _).comp (homotopy (X := X) _) +
      (homotopy n).comp (boundary n) = subdivide _ - LinearMap.id := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    have hm := congrArg (TopologicalSingular.map σ (n + 1)) (homotopyModel_identity n)
    simp_all [map_add, map_sub, map_sum, map_zsmul, map_boundary, push_face, map_single, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, simplexMap, ContinuousMap.comp_id, homotopy_single, subdivide_single, boundary_single, one_smul]
  exact DFunLike.congr_fun he c

theorem subdivide_naturality (f : C(X, Y)) n c :
    TopologicalSingular.map f n (subdivide n c) = subdivide n (TopologicalSingular.map f n c) :=
  fromModel_naturality _ f c
