/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.Equations
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import CCDN.Algebra.IdealZeroLocus
import CCDN.Projection.DegreePreservingProjectionCount
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {n d : ℕ} (I : Ideal (CoordinatePolynomial n))

/-- An eventually affine Hilbert function of positive slope is exactly the
one-dimensional case of the Hilbert dimension/degree predicate. -/
private theorem curve_dim_degree
    (hd : 0 < d) (h : HasFilteredCurveDegree I d) : HasAffineDimensionDegree I 1 d := by
  obtain ⟨N,c,hc⟩ := h
  have he : filteredHilbertPolynomial I = Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (c : ℚ) := by
    apply filteredHilbertPolynomial_eq_of_eventual
    refine ⟨N, fun k hk => ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact_mod_cast (hc k hk).symm
  have hne : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  constructor <;> rw [he]
  · exact Polynomial.natDegree_linear hne
  simpa using Polynomial.leadingCoeff_linear (b := (c : ℚ)) hne

/-- Count collisions for the bounded birational hypersurface projection in
dimension one. Only the defining equation is needed in the counting step. -/
theorem exists_bounded_projection_card_le [I.IsPrime]
    (hd : 0 < d) (hdegree : HasFilteredCurveDegree I d) :
    ∃ (b : Matrix (Fin 2) (Fin n) ℤ) (f : CoordinatePolynomial 2),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧ Irreducible f ∧ f.totalDegree = d ∧
      aeval (fun i => integerLinearForm (b i)) f ∈ I ∧
      ∀ S : Finset (Fin n → ℚ), (∀ z ∈ S, z ∈ idealZeroLocus I) →
        S.card ≤ (S.image (fun z i => eval z (integerLinearForm (b i)))).card + d * (d - 1) := by
  have hdim := curve_dim_degree I hd hdegree
  obtain ⟨_, _, hdimle, _⟩ := filteredHilbertPolynomial_positive_multiplicity I (Ideal.IsPrime.ne_top ‹I.IsPrime›)
  obtain ⟨b, f, hb, _, hP, hfd⟩ := exists_bounded_birational_hypersurface_projection_of_le 0 n
    (by simpa [hdim.natDegree_eq] using hdimle) I d hdim
  exact ⟨b, f, hb, hP.irreducible, hfd, hP.aeval_mem,
    degree_preserving_projection_card_le I _ (fun _ => linearForm_totalDegree_le _) d hd hdegree f
      hP.irreducible.ne_zero hfd hP.aeval_mem_iff⟩

end
end CCDN
