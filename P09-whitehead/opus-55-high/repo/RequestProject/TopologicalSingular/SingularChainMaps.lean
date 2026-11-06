/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularChains
import RequestProject.Tac


/-! # Functorial maps on the explicit singular chain groups -/


bwd

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def simplexMap (f : C(X, Y)) n (σ : Simplex X n) : Simplex Y n := f.comp σ

@[simp] theorem simplexMap_apply (f : C(X, Y)) n σ z :
    simplexMap f n σ z = f (σ z) := rfl

theorem face_simplexMap (f : C(X, Y)) {n} i σ :
    face i (simplexMap f (n + 1) σ) = simplexMap f n (face i σ) := rfl

noncomputable def map (f : C(X, Y)) n : Chain X n →ₗ[ℤ] Chain Y n :=
  Finsupp.lmapDomain ℤ ℤ (simplexMap f n)

@[simp] theorem map_single (f : C(X, Y)) n σ a :
    map f n (Finsupp.single σ a) = Finsupp.single (simplexMap f n σ) a :=
  Finsupp.mapDomain_single

theorem map_id n : map (ContinuousMap.id X) n = LinearMap.id := by
  aesop

theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) n :
    map (g.comp f) n = (map g n).comp (map f n) := by
  aesop

theorem map_boundary (f : C(X, Y)) n c :
    map f n (boundary n c) = boundary n (map f (n + 1) c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f _) := by
    apply Finsupp.lhom_ext
    grind [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_smul, face_simplexMap]
  exact DFunLike.congr_fun he c

theorem augmentation_map (f : C(X, Y)) c : augmentation (map f 0 c) = augmentation c := by
  have he : augmentation.comp (map f 0) = augmentation := by
    aesop
  exact DFunLike.congr_fun he c
