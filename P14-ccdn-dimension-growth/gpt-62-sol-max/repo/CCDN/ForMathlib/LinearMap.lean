/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Dimensions of images of linear maps

## Main results

* `LinearMap.finrank_map_add_finrank_inf_ker`: rank–nullity for the restriction of a linear map
  to a finite-dimensional subspace `V`: `finrank (V.map φ) + finrank (V ⊓ ker φ) = finrank V`.
* `LinearMap.finrank_span_range_le`: extending the scalars of the span of the image of a
  `K`-linear map `g : V → A` to a field `L` cannot increase its dimension beyond `finrank K V`.
* `LinearMap.finrank_span_range_le_of_ker_le`: the same bound by the rank of any linear map whose
  kernel is contained in the kernel of `g`.
-/

@[expose] public section

namespace LinearMap

variable {K M W : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] [AddCommGroup W]
  [Module K W]

/-- Rank–nullity for the restriction of a linear map to a finite-dimensional subspace. -/
theorem finrank_map_add_finrank_inf_ker (φ : M →ₗ[K] W) (V : Submodule K M)
    [FiniteDimensional K V] :
    Module.finrank K (V.map φ) + Module.finrank K ↥(V ⊓ ker φ) = Module.finrank K V := by
  have h := (φ.domRestrict V).finrank_range_add_finrank_ker
  rwa [range_domRestrict, ker_domRestrict, ← Submodule.finrank_map_subtype_eq V,
    Submodule.map_comap_subtype] at h

end LinearMap

namespace LinearMap

end LinearMap
