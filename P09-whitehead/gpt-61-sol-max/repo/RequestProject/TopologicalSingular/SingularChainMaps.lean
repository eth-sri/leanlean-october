import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.SingularChains

/-! # Functorial maps on the explicit singular chain groups -/


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular




variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

  (f : C(X, Y))
def simplexMap  (n : ℕ) (σ : Simplex X n)  := f.comp σ





noncomputable def map  (n : ℕ)  :=
  Finsupp.lmapDomain ℤ ℤ (simplexMap f n)

@[simp] theorem map_single  (n : ℕ) (σ : Simplex X n) (a : ℤ) :
    map f n (Finsupp.single σ a) = Finsupp.single (simplexMap f n σ) a :=
  Finsupp.mapDomain_single

theorem map_id (n : ℕ) : map (ContinuousMap.id X) n = LinearMap.id := by
  aesop

theorem map_comp  (g : C(Y, Z)) (n : ℕ) :
    map (g.comp f) n = (map g n).comp (map f n) := by
  aesop

theorem map_boundary  (n : ℕ) (c : Chain X (n + 1)) :
    map f n (boundary n c) = boundary n (map f (n + 1) c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f (n + 1)) := by
    aesop (add simp [boundary_single])
  exact DFunLike.congr_fun he c

theorem augmentation_map  (c : Chain X 0) : augmentation (map f 0 c) = augmentation c := by
  aesop (add simp [map, augmentation])

end FiniteChains.TopologicalSingular
