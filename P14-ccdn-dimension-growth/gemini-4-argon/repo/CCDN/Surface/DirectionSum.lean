/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.ProjectiveZeroLocus
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Plane.ProjectivePlaneLinearCount

/-! The reciprocal heights of distinct rational projective points on a
plane curve of degree at least three have a uniform, coefficient-independent
sum. Geometric height bands turn the proved projective point count into
the weighted estimate used for surface-line directions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

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
  classical
  have hC := projectivePlaneAbsoluteConstant_pos
  refine ⟨9 * projectivePlaneAbsoluteConstant, mul_pos (by norm_num) hC, ?_⟩
  intro d hd F hF hir s hs
  let f := map (Int.castRingHom ℚ) F
  have hf : f.IsHomogeneous d := hF.map _
  have hirq : Irreducible f := rational_irreducible_of_charZero_map F hir
  have hd0 : (0 : ℝ) < d := mod_cast (show 0 < d by omega)
  have hd3 : (3 : ℝ) ≤ d := mod_cast hd
  let M := projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4
  have hM : 0 ≤ M := by positivity
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ x ∈ s, x.mulHeight) (show (1 : ℝ) < 8 by norm_num)
  have hgeom (N : ℕ) (s : Finset (ProjectivePoint 2))
      (hmax : ∀ x ∈ s, x.mulHeight ≤ (8 : ℝ) ^ N)
      (hcount : ∀ k : ℕ, ((s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card : ℝ) ≤ M * 4 ^ k) :
      ∑ x ∈ s, 1 / x.mulHeight ≤ 9 * M - 8 * M * (1 / 2 : ℝ) ^ N := by
    induction N generalizing s with
    | zero =>
      have he (x : ProjectivePoint 2) (hx : x ∈ s) : x.mulHeight = 1 := by
        have := hmax x hx; have := x.one_le_mulHeight; norm_num at *; linarith
      have hc := hcount 0
      rw [Finset.filter_eq_self.mpr hmax] at hc
      have hsum : ∑ x ∈ s, 1 / x.mulHeight = (s.card : ℝ) :=
        (Finset.sum_congr rfl fun x hx => by rw [he x hx, div_one]).trans (by simp)
      rw [hsum]
      simpa only [pow_zero, mul_one, show 9 * M - 8 * M = M by ring] using hc
    | succ N ih =>
      let t := s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ N)
      let u := s.filter (fun x => ¬x.mulHeight ≤ (8 : ℝ) ^ N)
      have ht := ih t (fun x hx => (Finset.mem_filter.mp hx).2) fun k =>
        (mod_cast (Finset.card_le_card fun x hx =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1,
            (Finset.mem_filter.mp hx).2⟩) :
          ((t.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
            (s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card).trans (hcount k)
      have hscard : (s.card : ℝ) ≤ M * 4 ^ (N + 1) := by
        simpa only [Finset.filter_eq_self.mpr hmax] using hcount (N + 1)
      have hu : ∑ x ∈ u, 1 / x.mulHeight ≤ 4 * M * (1 / 2 : ℝ) ^ N := calc
        _ ≤ ∑ _x ∈ u, 1 / (8 : ℝ) ^ N := Finset.sum_le_sum fun x hx =>
          one_div_le_one_div_of_le (by positivity) (le_of_not_ge (Finset.mem_filter.mp hx).2)
        _ = (u.card : ℝ) / (8 : ℝ) ^ N := by simp [div_eq_mul_inv]
        _ ≤ (s.card : ℝ) / (8 : ℝ) ^ N := div_le_div_of_nonneg_right
          (mod_cast Finset.card_le_card (Finset.filter_subset _ s)) (by positivity)
        _ ≤ (M * 4 ^ (N + 1)) / (8 : ℝ) ^ N := div_le_div_of_nonneg_right hscard (by positivity)
        _ = 4 * M * (1 / 2 : ℝ) ^ N := by
          rw [pow_succ, show M * (4 ^ N * 4) / (8 : ℝ) ^ N = 4 * M * ((4 : ℝ) ^ N / (8 : ℝ) ^ N) by ring,
            ← div_pow]
          norm_num
      have he := Finset.sum_filter_add_sum_filter_not s (fun x => x.mulHeight ≤ (8 : ℝ) ^ N)
        (fun x => 1 / x.mulHeight)
      rw [pow_succ]; linarith
  have hh := hgeom N s
    (fun x hx => (Finset.single_le_sum (fun y _ => zero_le_one.trans y.one_le_mulHeight) hx).trans hN.le)
    fun k => by
      have hB : (1 : ℝ) ≤ 8 ^ k := one_le_pow₀ (by norm_num)
      have hcR : ((s.filter (fun x => x.mulHeight ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
          (projectiveCount (projectiveZeroLocus f) ((8 : ℝ) ^ k) : ℝ) :=
        mod_cast Finset.card_le_card fun x hx =>
          mem_projectivePoints.mpr ⟨(Finset.mem_filter.mp hx).2, hs x (Finset.mem_filter.mp hx).1⟩
      have he8 : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := calc
        _ = ((2 : ℝ) ^ (3 : ℝ)) ^ (2 / 3 : ℝ) := by norm_num
        _ = (2 : ℝ) ^ ((3 : ℝ) * (2 / 3 : ℝ)) := (Real.rpow_mul (by norm_num) _ _).symm
        _ = 4 := by norm_num
      have hp : ((8 : ℝ) ^ k) ^ (2 / (d : ℝ)) ≤ (4 : ℝ) ^ k := calc
        _ ≤ ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hB
          ((div_le_div_iff₀ hd0 (by norm_num)).mpr (by nlinarith))
        _ = (4 : ℝ) ^ k := by
          rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (k : ℝ),
            Real.rpow_mul_natCast (by norm_num), he8]
      exact (hcR.trans (projective_plane_equation_bound f hf (by omega) hirq hB)).trans
        (mul_le_mul_of_nonneg_left hp hM)
  have hnonneg : 0 ≤ 8 * M * (1 / 2 : ℝ) ^ N := by positivity
  dsimp only [M] at hh
  linarith

end
end CCDN
