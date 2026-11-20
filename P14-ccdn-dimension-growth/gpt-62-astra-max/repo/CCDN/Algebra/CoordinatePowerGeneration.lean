/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection

/-! Balanced coordinate-power reductions imply eventual generation by a
linear parameter in arbitrary ambient dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) {m n : ℕ}

/-- The degree filtration of the coordinate ring `MvPolynomial σ K ⧸ I` is increasing. -/
lemma filteredCoordinateSpace_mono (hmn : m ≤ n) :
    filteredCoordinateSpace I m ≤ filteredCoordinateSpace I n := by
  apply Submodule.map_mono
  intro f hf
  exact (mem_restrictTotalDegree _ _ _).mpr (((mem_restrictTotalDegree _ _ _).mp hf).trans hmn)

variable [Fintype σ]

end
end CCDN
