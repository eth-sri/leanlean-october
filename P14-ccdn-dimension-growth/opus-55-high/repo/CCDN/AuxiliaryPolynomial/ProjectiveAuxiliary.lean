/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousChart
import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.Determinant.HeightDeterminant
import CCDN.Height.CountingHypotheses
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryDegree
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryLargeHeight
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary
import CCDN.Determinant.HomogeneousDeterminantComparison
import CCDN.Determinant.ProjectiveHeightDeterminant

/-!
Homogeneous auxiliary polynomials for bounded primitive projective points,
with explicit degrees in both coefficient-height ranges.

The coefficient-sensitive determinant comparison for bounded primitive
integer representatives of projective plane points.
-/

namespace CCDN
open MvPolynomial

theorem projective_no_auxiliary_height_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 2 ≤ d) (hdM : d ≤ M)
    {H : ℝ} (hchart : IsBoundedPlaneCurve K (affineChart 2 f) d H)
    {B : ℝ} {z : Fin t → IntPoint 3} (hzB : IsPrimitiveBoxZeroFamily f B z)
    (hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 2 * s + d ^ 2 = d * (2 * M + 3) ∧
      (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
        Real.log (1 + Real.log H / (d : ℝ) ^ 2) -
          heightDeterminantError projectivePlaneDeterminantConstant) ≤
        Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  obtain ⟨s, a, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hzB.eval_eq_zero
      hzB.one_le_radius hzB.abs_le hrel
  have hs := (plane_homogeneous_rank_bounds (by grind) hdM hr).1
  refine ⟨s, plane_homogeneous_rank_identity hdM hr, ?_⟩
  let F := fun j => (monomial (homogeneousMonomials 2 M j) 1 : MvPolynomial (Fin 3) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree 2 M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials 2 M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
    rwa [he]
  rw [← he] at hupper
  refine le_trans ?_ hupper
  have hdeg := hchart.totalDegree_eq
  obtain ⟨bad, hmem, hcharge⟩ := exists_plane_bad_prime_set (affineChart 2 f)
    (by omega) hchart.irreducible H hchart.one_le_height hchart.coeff_le
  rw [hdeg] at hmem hcharge
  have hred (p : ℕ) (hp : p ∈ ((Finset.Ioc 0 s).filter Nat.Prime) \ bad)
      (hlo : stepanovThreshold (d : ℝ) < p) :
      Irreducible (map (Int.castRingHom (ZMod p)) f) := by
    let : Fact p.Prime := ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2⟩
    apply homogeneous_irreducible_reduction_of_not_hypersurfaceBadReduction f hf hdeg
    intro hbad
    exact (Finset.mem_sdiff.mp hp).2 ((hmem p).mpr ⟨hlo, hbad⟩)
  have hlower := projective_determinant_log_lower_at_rank (z := z ∘ a) hs f hf hd
    ⟨hF, fun i => hzB.primitive (a i), fun i => hzB.eval_eq_zero (a i), hi'⟩ bad hred
  have hh := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
  dsimp only [heightDeterminantError]
  nlinarith

end CCDN
