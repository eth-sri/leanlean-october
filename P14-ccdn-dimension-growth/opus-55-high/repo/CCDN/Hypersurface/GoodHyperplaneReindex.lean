/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Hypersurface.GraphHyperplaneRestriction
import CCDN.Hypersurface.GoodHyperplaneBounds

/-! Transport of the constructed good hyperplane to coordinates suited to
the universal Noether family. -/

namespace CCDN
section
open MvPolynomial

/-- Restriction to the graph hyperplane `x_none = ∑ a j * x j` commutes with renaming the
coordinates along an equivalence `e`. -/
lemma graphHyperplaneRestriction_rename {K σ τ : Type*}
    [CommRing K] [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (a : τ → K) (f : MvPolynomial (Option σ) K) :
    rename e (graphHyperplaneRestriction (a ∘ e) f) =
      graphHyperplaneRestriction a (rename (Equiv.optionCongr e) f) := by
  have he : (rename e).toRingHom.comp
      (graphHyperplaneRestriction (a ∘ e)).toRingHom =
      (graphHyperplaneRestriction a).toRingHom.comp
        (rename (Equiv.optionCongr e)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro i
      cases i with
      | none =>
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          graphHyperplaneRestriction, aeval_X, Option.elim_none, map_sum, map_mul,
          rename_C, rename_X, Function.comp_apply, Equiv.optionCongr_apply]
        exact e.sum_comp (fun j => C (a j) * X j)
      | some i => simp [graphHyperplaneRestriction]
  exact RingHom.congr_fun he f

