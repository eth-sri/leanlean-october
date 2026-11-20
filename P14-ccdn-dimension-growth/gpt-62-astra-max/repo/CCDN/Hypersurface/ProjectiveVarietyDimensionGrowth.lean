/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Projection.ProjectiveProjectionGrowth
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.HomogeneousProjectionEquation

/-! Dimension growth for homogeneous prime ideals of positive
projective dimension. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The general projective-variety bound, with dimension and codimension
displayed separately. The hypotheses use the Hilbert polynomial of
the coordinate ring. -/
theorem projective_variety_dimension_growth (m k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (CoordinatePolynomial (m + k + 2)), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d → HasProjectiveDimensionDegree I (m + 1) d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ projectionDegreeExponent m k * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_projection_dimension_growth m k
  refine ⟨C, hC, ?_⟩
  intro I hprime hI d hd hdimdeg B hB
  obtain ⟨b, f, hb, hN, hP, hfdeg⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le (m + 1) (m + k + 2)
      (by omega) I d hdimdeg
  have hfhom := homogeneous_projection_equation I hI _ (fun i => linearForm_isHomogeneous (fun j => (b i j : ℚ))) f hP.irreducible.ne_zero hP.ker_eq
  rw [hfdeg] at hfhom
  apply hcount I d hd b hb f hP.irreducible hfhom hfdeg hP.aeval_mem _ B hB
  intro z s hzero hproj
  exact (linear_normalization_fiber_card_le I
    (fun i : Fin (m + 2) => integerLinearForm (b i.succ))
    (fun i => linearForm_totalDegree_le _) hN.injective hN.integral d hdimdeg
    (fun i => z i.succ) s hzero (by solve_by_elim)).trans
    (by bound)

end
end CCDN
