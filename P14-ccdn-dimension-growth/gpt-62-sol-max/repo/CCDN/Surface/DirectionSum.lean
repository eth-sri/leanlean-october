/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Plane.ProjectivePlaneCount
import CCDN.Analysis.GeometricShells

/-! The reciprocal heights of distinct rational projective points on a
plane curve of degree at least three have a uniform, coefficient-independent
sum. Geometric height bands turn the proved projective point count into
the weighted estimate used for surface-line directions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable {α : Type*}
  (s : Finset α) (h : α → ℝ) (M : ℝ)
include α s h M

/-- A finite weighted-count lemma with geometric counting thresholds. -/
private theorem sum_inv_height_le_of_geometric_count (hM : 0 ≤ M)
    (hheight : ∀ x ∈ s, 1 ≤ h x)
    (hcount : ∀ k : ℕ,
      ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤ M * 4 ^ k) :
    ∑ x ∈ s, 1 / h x ≤ 9 * M := by
  classical
  have hgeom := sum_le_of_geometric_shells s h (fun x => 1 / h x) one_pos
    (q := 8) (C := 4 * M) (D := M) (by norm_num) (by positivity)
  refine (hgeom ?_ ?_).trans_eq (by ring)
  · simpa using (calc
      ∑ x ∈ s.filter (fun x => h x ≤ 1), 1 / h x ≤ ∑ _x ∈ s.filter (fun x => h x ≤ 1), (1 : ℝ) :=
        Finset.sum_le_sum fun x hx => by simpa using
          (one_div_le_one_div_of_le one_pos (hheight x (Finset.mem_filter.mp hx).1))
      _ ≤ M := by simpa using hcount 0)
  · intro n
    let A := s.filter (fun x => 1 * (8 : ℝ) ^ n < h x ∧ h x ≤ 1 * (8 : ℝ) ^ (n + 1))
    have hcard : (A.card : ℝ) ≤ M * 4 ^ (n + 1) := by
      refine (Nat.cast_le.mpr (Finset.card_le_card (t := s.filter (fun x => h x ≤ (8 : ℝ) ^ (n + 1))) ?_)).trans
        (hcount (n + 1))
      intro x hx
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, by simpa using (Finset.mem_filter.mp hx).2.2⟩
    calc
      _ ≤ ∑ _x ∈ A, 1 / (8 : ℝ) ^ n := Finset.sum_le_sum fun x hx =>
        one_div_le_one_div_of_le (by positivity) (by simpa using (Finset.mem_filter.mp hx).2.1.le)
      _ ≤ M * 4 ^ (n + 1) / (8 : ℝ) ^ n := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ ((8 : ℝ) ^ n)⁻¹)
      _ = _ := by rw [pow_succ, show (1 / 2 : ℝ) = 4 / 8 by norm_num, div_pow]; ring

end

private lemma eight_pow_two_thirds (k : ℕ) :
    ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) = (4 : ℝ) ^ k := by
  have he : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by
    norm_num
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (k : ℝ),
    Real.rpow_mul_natCast (by norm_num), he]

/-- A uniform reciprocal-height sum for distinct rational projective
zeros. The constant precedes the equation, its degree and the finite set. -/
private theorem projective_plane_reciprocal_height_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 3 ≤ d →
      ∀ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d → Irreducible f →
      ∀ s : Finset (ProjectivePoint 2), (∀ x ∈ s, x ∈ projectiveZeroLocus f) →
        ∑ x ∈ s, 1 / x.mulHeight ≤ C * (d : ℝ) ^ 4 := by
  classical
  refine ⟨9 * projectivePlaneAbsoluteConstant, by
    exact mul_pos (by norm_num) projectivePlaneAbsoluteConstant_pos, ?_⟩
  intro d hd f hf hir s hs
  have hC := projectivePlaneAbsoluteConstant_pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h := sum_inv_height_le_of_geometric_count s (fun x => x.mulHeight)
    (projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4)
    (by positivity) (fun x _ => x.one_le_mulHeight) ?_
  · convert h using 1
    ring
  intro k
  have hB : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
  have hc : (s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card ≤
      projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxs, hheight⟩ := Finset.mem_filter.mp hx
    exact mem_projectivePoints.mpr ⟨hheight, hs x hxs⟩
  have hcR : ((s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
      (projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) : ℝ) := by exact_mod_cast hc
  have hp : ((8 : ℝ) ^ k) ^ (2 / (d : ℝ)) ≤ (4 : ℝ) ^ k := by
    calc
      _ ≤ ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB
        ((div_le_div_iff₀ hd0 (by norm_num)).mpr (by nlinarith))
      _ = _ := eight_pow_two_thirds k
  exact (hcR.trans (projective_plane_equation_bound f hf (by omega) hir hB)).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

/-- There is an absolute constant `C` such that, for every absolutely irreducible integer
homogeneous polynomial `F` of degree `d ≥ 3` in three variables, the sum of the reciprocal
multiplicative heights of any finite set of rational points of the plane curve `F = 0` is at
most `C d⁴`; no primitivity or coefficient-height hypothesis is needed. -/
theorem integer_projective_plane_reciprocal_height_sum :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ), 3 ≤ d →
      ∀ F : MvPolynomial (Fin 3) ℤ, F.IsHomogeneous d →
      AbsolutelyIrreducible F →
      ∀ s : Finset (ProjectivePoint 2),
        (∀ x ∈ s, x ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) F)) →
        ∑ x ∈ s, 1 / x.mulHeight ≤ C * (d : ℝ) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := projective_plane_reciprocal_height_sum
  refine ⟨C, hC, ?_⟩
  intro d hd F hF hir s hs
  exact hbound d hd (map (Int.castRingHom ℚ) F) (hF.map _)
    (rational_irreducible_of_charZero_map F hir) s hs

end
end CCDN
