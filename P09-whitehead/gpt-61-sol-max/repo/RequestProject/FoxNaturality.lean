import Mathlib.Tactic

import RequestProject.Fox

/-!
# Naturality of the Fox derivative under an inclusion of generators

When a two-complex `X` is enlarged to `X'` by adding cells, the one-cells of `X` are
one-cells of `X'` and a relator of `X` is read in `X'` as the same word.  The Fox boundary
matrix of `X'` therefore restricts, on the old cells, to the boundary matrix of `X`, and
the boundary of an old relator has no component along a new generator.

This file proves the two corresponding statements for an injective map of generating sets
`f : α → β`:

* `FiniteChains.fox_map` — `∂(f_*w)/∂y_{f i} = f_*(∂w/∂x_i)`;
* `FiniteChains.fox_map_of_not_mem_range` — `∂(f_*w)/∂y_b = 0` for `b` outside the image
  of `f`.
-/

namespace FiniteChains



variable {α β : Type*} [DecidableEq α] [DecidableEq β]

  (f : α → β)
/-- The ring homomorphism of group rings induced by a map of generating sets. -/
noncomputable def freeRingMap   :=
  MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map f)

omit [DecidableEq α] [DecidableEq β] in
@[simp] theorem freeRingMap_grp  (w : FreeGroup α) :
    freeRingMap f (grp w) = grp (FreeGroup.map f w) := MonoidAlgebra.mapDomain_single


/-- **Naturality of the Fox derivative.**  For an injective map of generating sets the
derivative of the image word with respect to the image generator is the image of the
derivative. -/
theorem fox_map  (hf : Function.Injective f) (i : α) (w : FreeGroup α) :
    fox (f i) (FreeGroup.map f w) = freeRingMap f (fox i w) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => by_cases h : i = k <;> simp [h, hf.eq_iff]
  | inv_of k ih =>
      aesop (add simp [fox_inv])
  | mul u v hu hv =>
      simp_all [fox_mul]

omit [DecidableEq α] in
/-- The derivative of an old word with respect to a new generator vanishes. -/
theorem fox_map_of_not_mem_range  {b : β} (hb : ∀ i, b ≠ f i) (w : FreeGroup α) :
    fox b (FreeGroup.map f w) = 0 := by
  induction w using FreeGroup.induction_on <;> simp_all [fox_inv, fox_mul]

end FiniteChains
