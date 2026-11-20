module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChains

@[expose] public section

/-! # Functorial maps on the explicit singular chain groups -/

namespace FiniteChains.TopologicalSingular

open Set Topology

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (f : C(X, Y))

variable (n : ℕ) (σ : Simplex X n)

def simplexMap := f.comp σ

@[simp] theorem simplexMap_apply (z : Domain n) :
    simplexMap f n σ z = f (σ z) := rfl

theorem face_simplexMap {n : ℕ} (i : Fin _) (σ : Simplex X _) :
    face i (simplexMap f _ σ) = simplexMap f n (face i σ) := rfl

variable (n : ℕ)

noncomputable def map :=
  Finsupp.lmapDomain ℤ ℤ (simplexMap f n)

@[simp] theorem map_single (σ : Simplex X n) (a : ℤ) :
    map f n (Finsupp.single σ a) = Finsupp.single (simplexMap f n σ) a :=
  Finsupp.mapDomain_single

theorem map_id (n : ℕ) : map (ContinuousMap.id X) n = LinearMap.id := by
  aesop

variable (f : C(X, Y))

theorem map_comp (g : C(Y, Z)) (n : ℕ) :
    map (g.comp f) n = (map g n).comp (map f n) := by
  aesop

theorem map_boundary (n : ℕ) (c : Chain X _) :
    map f n (boundary n c) = boundary n (map f _ c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f _) := by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_smul,
      face_simplexMap]
  exact DFunLike.congr_fun he c

theorem augmentation_map (c : Chain X 0) : augmentation (map f 0 c) = augmentation c := by
  have he : augmentation.comp (map f 0) = augmentation := by
    apply Finsupp.lhom_ext
    simp
  exact DFunLike.congr_fun he c

end FiniteChains.TopologicalSingular
