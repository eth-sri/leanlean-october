/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! A proper section bounds independent classes in any algebra-valued image,
not only distinct point evaluations. This is the multiplicity-ready form of
the Hilbert-function argument. -/

@[expose] public section
namespace CCDN
noncomputable section

open MvPolynomial

section
variable {K B σ ι : Type*} [Field K]
  [CommRing B] [Algebra K B] [Fintype σ] [Fintype ι]
  (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
include K B σ ι p

/-- Independent polynomial images in a proper section number at most d*m.
This applies to truncated local expansions as well as to point values. -/
theorem section_image_rank_le
    (d : ℕ) (hdegree : HasFilteredCurveDegree p d)
    (φ : (MvPolynomial σ K ⧸ p) →ₐ[K] B) (h : ι → MvPolynomial σ K)
    (hlin : LinearIndependent K (fun i => φ ((Ideal.Quotient.mk p) (h i))))
    (l : MvPolynomial σ K) (hl : l ∉ p) (m : ℕ) (hld : l.totalDegree ≤ m)
    (hzero : φ ((Ideal.Quotient.mk p) l) = 0) : Fintype.card ι ≤ d * m := by
  classical
  obtain ⟨N₀, c, hc⟩ := hdegree
  let N := max N₀ (Finset.univ.sup fun i => (h i).totalDegree)
  let V := (filteredCoordinateSpace p (m + N)).map φ.toLinearMap
  have hmem (i : ι) : φ ((Ideal.Quotient.mk p) (h i)) ∈ V := by
    refine Submodule.mem_map.mpr ⟨_, Submodule.mem_map.mpr ⟨h i, ?_, rfl⟩, rfl⟩
    rw [mem_restrictTotalDegree]
    exact (Finset.le_sup (f := fun i => (h i).totalDegree) (Finset.mem_univ i)).trans (by grind)
  have hi := LinearIndependent.of_comp V.subtype
    (v := fun i => (⟨_, hmem i⟩ : V)) hlin
  have hcard := hi.fintype_card_le_finrank
  have hrank := filtered_section_image_finrank_add_le p φ hl hld hzero N
  have h₁ := hc N (le_max_left _ _)
  have h₂ := hc (m + N) (by dsimp [N]; grind)
  change Module.finrank K V + _ ≤ _ at hrank
  exact_mod_cast (show (Fintype.card ι : ℤ) ≤ (d : ℤ) * (m : ℤ) by
    push_cast at h₂
    nlinarith [show (Fintype.card ι : ℤ) ≤ Module.finrank K V by exact_mod_cast hcard,
      show (Module.finrank K V : ℤ) + (Module.finrank K (filteredCoordinateSpace p N) : ℤ) ≤
        Module.finrank K (filteredCoordinateSpace p (m + N)) by exact_mod_cast hrank])

end

end
end CCDN
