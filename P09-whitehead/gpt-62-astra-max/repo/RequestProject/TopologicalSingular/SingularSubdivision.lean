module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularSubdivisionModels

@[expose] public section

/-! # Barycentric subdivision of actual singular chains

The universal affine chains are pushed forward by each continuous
singular simplex. The operator commutes with boundary and is naturally
chain homotopic to the identity. No mesh or excision conclusion is assumed.
-/

noncomputable section

namespace FiniteChains.SingularSubdivision

open TopologicalSingular AffineVertexChains

universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {k l : ℕ} (m : Chain (Domain k) l)

def fromModel :=
  Finsupp.linearCombination ℤ (fun σ : Simplex X k => TopologicalSingular.map σ l m)

theorem fromModel_single (σ : Simplex X k) (r : ℤ) :
    fromModel m (Finsupp.single σ r) = r • TopologicalSingular.map σ l m :=
  by apply Finsupp.linearCombination_single

theorem fromModel_naturality (f : C(X, Y)) (c : Chain X k) :
    TopologicalSingular.map f l (fromModel m c) = fromModel m (TopologicalSingular.map f k c) := by
  have he : (TopologicalSingular.map f l).comp (fromModel m) =
      (fromModel m).comp (TopologicalSingular.map f k) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [LinearMap.comp_apply, fromModel_single, one_smul, map_single]
    exact (DFunLike.congr_fun (map_comp σ f l) m).symm
  exact DFunLike.congr_fun he c

variable (n : ℕ)

def subdivide : Chain X n →ₗ[ℤ] Chain X n := fromModel (model n)

def homotopy : Chain X n →ₗ[ℤ] Chain X (n + 1) := fromModel (homotopyModel n)

variable (σ : Simplex X n) (r : ℤ)

theorem subdivide_single :
    subdivide n (Finsupp.single σ r) = r • TopologicalSingular.map σ n (model n) := by apply fromModel_single

theorem homotopy_single :
    homotopy n (Finsupp.single σ r) = r • TopologicalSingular.map σ _ (homotopyModel n) :=
  by apply fromModel_single

theorem push_face {n k : ℕ} (σ : Simplex X _) (i : Fin _) (c : Chain (Domain n) k) :
    TopologicalSingular.map σ k (TopologicalSingular.map (standardMap i.succAbove) k c) =
      TopologicalSingular.map (face i σ) k c :=
  (DFunLike.congr_fun (map_comp _ σ k) c).symm

variable (n : ℕ) (c : Chain X (n + 1))

theorem subdivide_boundary :
    subdivide n (boundary n c) = boundary n (subdivide _ c) := by
  have he : (subdivide n).comp (boundary n) = (boundary n).comp (subdivide (X := X) _) := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    simp only [LinearMap.comp_apply, boundary_single, map_sum, map_zsmul, subdivide_single, one_smul]
    rw [← map_boundary, boundary_model]
    simp only [map_sum, map_zsmul, push_face]
  exact DFunLike.congr_fun he c

theorem homotopy_identity_succ :
    boundary _ (homotopy _ c) + homotopy n (boundary n c) = subdivide _ c - c := by
  have he : (boundary (n + 1)).comp (homotopy (X := X) _) +
      (homotopy n).comp (boundary n) = subdivide (n + 1) - LinearMap.id := by
    apply VertexChains.linearMap_ext_basis
    intro σ
    have hm := congrArg (TopologicalSingular.map σ (n + 1)) (homotopyModel_identity n)
    simp only [map_add, map_sub, map_sum, map_zsmul, map_boundary, push_face, map_single] at hm
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      simplexMap, ContinuousMap.comp_id, homotopy_single, subdivide_single, boundary_single, map_sum, map_zsmul, one_smul] using hm
  exact DFunLike.congr_fun he c

theorem subdivide_naturality (f : C(X, Y)) (n : ℕ) (c : Chain X n) :
    TopologicalSingular.map f n (subdivide n c) = subdivide n (TopologicalSingular.map f n c) :=
  by apply fromModel_naturality

end FiniteChains.SingularSubdivision
