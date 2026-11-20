/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.Projection.ProjectiveProjectionGrowth
import CCDN.Projection.ZeroDimensionalProjectiveCount
import CCDN.Hilbert.ProperHilbertDimension
import CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth
import CCDN.Plane.ProjectivePlaneCount

/-! The projective bound combines the count in dimension zero, the direct hypersurface
bound, and bounded projection to hypersurfaces (including plane curves). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private def equationDegreeExponent (m : ℕ) : ℕ := if m = 0 then 4 else 18 + 3 * m

private theorem projected_equation_growth (m : ℕ) :
    ProjectiveHypersurfaceGrowth m (equationDegreeExponent m) := by
  cases m with
  | zero =>
    refine ⟨projectivePlaneAbsoluteConstant, projectivePlaneAbsoluteConstant_pos,
      fun f hf hir hd B hB => ?_⟩
    simpa [equationDegreeExponent] using
      (projective_plane_equation_bound f hf (by omega) hir hB).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_one_le hB
          ((div_le_one (by positivity)).mpr (by exact_mod_cast (show 2 ≤ f.totalDegree by omega))))
          (mul_nonneg projectivePlaneAbsoluteConstant_pos.le (by positivity)))
  | succ m => simpa [equationDegreeExponent] using projective_hypersurface_dimension_growth (m + 1)

/-- The degree exponent of Theorem 1 in `ℙⁿ`. -/
def projectiveGrowthExponent (n : ℕ) : ℕ := 2 * n ^ 2 + 5 * n - 5

/-- CCDN Theorem 1, with degree exponent `2n² + 5n - 5` in `ℙⁿ`. -/
theorem projective_dimension_growth (n : ℕ) :
    ProjectiveGrowth n (projectiveGrowthExponent n) := by
  choose C _ hc using fun m : Fin n => (projected_equation_growth m).projected n
  obtain ⟨T, hT⟩ := (Set.finite_range C).bddAbove
  obtain ⟨Ch, hCh, hh⟩ := (projective_hypersurface_dimension_growth (n - 2)).ideal
  let K := max T 0 + Ch + 1
  have hK : 1 ≤ K := by grind
  refine ⟨K, by linarith, fun I hprime hI d hd hdegree B hB => ?_⟩
  let r := (filteredHilbertPolynomial I).natDegree
  change _ = (d : ℚ) / r.factorial at hdegree
  change _ ≤ _ * B ^ (r - 1)
  have hr : r ≤ n := by
    have h := hilbert_dimension_lt_ambient_of_degree_gt_one I hprime.ne_top d (by omega) hdegree
    simp only [Fintype.card_fin] at h
    change r < n + 1 at h
    omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have absorb {c : ℝ} {e : ℕ} (hc : c ≤ K) (he : e ≤ projectiveGrowthExponent n)
      (h : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        c * (d : ℝ) ^ e * B ^ (r - 1)) :=
    h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hc (pow_le_pow_right₀ hdR he) (by positivity) (by positivity)) (by positivity))
  by_cases hsmall : r ≤ 1
  · apply absorb (e := 0) hK (Nat.zero_le _)
    have he : r - 1 = 0 := by omega
    simp only [he, pow_zero, mul_one]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsmall with h0 | h1
    · rw [projectiveIdealZeroLocus_eq_empty_of_hilbert_dimension_zero I h0]
      simp [projectiveCount, projectivePoints]
    · exact_mod_cast zero_dimensional_projective_count_le I h1 B
  have hdim (m : ℕ) (hm : r = m + 2) : HasProjectiveDimensionDegree I (m + 1) d :=
    ⟨hm, by simpa only [hm] using hdegree⟩
  by_cases hs : r = n ∧ 3 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp only [Nat.add_sub_cancel_right] at hh
    refine absorb (c := Ch) (e := 18 + 3 * k) (by grind) ?_ ?_
    · unfold projectiveGrowthExponent
      have : 9 ≤ (k + 2) ^ 2 := by nlinarith [hs.2]
      omega
    · rw [show r - 1 = k + 1 by omega]
      exact hh I hprime hI d hd (hdim k hs.1) B hB
  let m : Fin n := ⟨r - 2, by omega⟩
  have hm : r = (m : ℕ) + 2 := by dsimp [m]; omega
  refine absorb (c := C m) (e := equationDegreeExponent m + 1 + 2 * (n + 1) * ((m : ℕ) + 1))
    ((hT (Set.mem_range_self m)).trans (by grind)) ?_ ?_
  · unfold equationDegreeExponent projectiveGrowthExponent
    split_ifs with h0
    · rw [h0]
      have : 4 ≤ n ^ 2 := by nlinarith
      omega
    · have h := Nat.mul_le_mul_left (2 * (n + 1)) (show (m : ℕ) + 3 ≤ n by omega)
      have hp : 5 ≤ 2 * n ^ 2 + 5 * n := by omega
      nlinarith [Nat.sub_add_cancel hp]
  · rw [show r - 1 = (m : ℕ) + 1 by omega]
    exact hc m I hprime hI d hd (hdim m hm) B hB

end
end CCDN
