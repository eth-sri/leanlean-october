/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Height.ProjectiveZeroLocus
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Plane.ProjectivePlaneLinearCount

/-! The reciprocal heights of distinct rational projective points on a
plane curve of degree at least three have a uniform, coefficient-independent
sum. Geometric height bands turn the proved projective point count into
the weighted estimate used for surface-line directions. -/

namespace CCDN
open MvPolynomial

section
variable {α : Type*} (s : Finset α) (h : α → ℝ) (M : ℝ)

theorem sum_inv_height_geometric_bound
    (_hM : 0 ≤ M) (N : ℕ)
    (hheight : ∀ x ∈ s, 1 ≤ h x)
    (hmax : ∀ x ∈ s, h x ≤ (8 : ℝ) ^ N)
    (hcount : ∀ k : ℕ,
      ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤ M * 4 ^ k) :
    ∑ x ∈ s, 1 / h x ≤ 9 * M - 8 * M * (1 / 2 : ℝ) ^ N := by
  induction N generalizing s with
  | zero =>
    have he (x : α) (hx : x ∈ s) : h x = 1 := by grind
    have hs : s.filter (fun x => h x ≤ (8 : ℝ) ^ 0) = s := by grind
    have hc := hcount 0
    rw [hs] at hc
    have hsum : ∑ x ∈ s, 1 / h x = s.card := by simp_all
    rw [hsum]
    simpa [pow_zero, mul_one, show 9 * M - 8 * M = M by ring] using hc
  | succ N ih =>
    let t := s.filter (fun x => h x ≤ (8 : ℝ) ^ N)
    let u := s.filter (fun x => ¬h x ≤ (8 : ℝ) ^ N)
    have ht : ∑ x ∈ t, 1 / h x ≤ 9 * M - 8 * M * (1 / 2 : ℝ) ^ N := by
      apply ih t
      · grind
      · grind
      · intro k
        have hs : (t.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card ≤
            (s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card := by
          apply Finset.card_le_card
          intro x hx
          obtain ⟨hx, hk⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hk⟩
        exact (show ((t.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤
          ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) by
            exact_mod_cast hs).trans (hcount k)
    have hscard : s.card ≤ M * 4 ^ (N + 1) := by
      have hs :=
        Finset.filter_eq_self.mpr hmax
      grind
    have hu : ∑ x ∈ u, 1 / h x ≤ 4 * M * (1 / 2 : ℝ) ^ N := by
      calc
        _ ≤ ∑ _x ∈ u, 1 / (8 : ℝ) ^ N := by
          apply Finset.sum_le_sum
          intro x hx
          exact one_div_le_one_div_of_le (by positivity)
            (le_of_not_ge (Finset.mem_filter.mp hx).2)
        _ = u.card / (8 : ℝ) ^ N := by aesop
        _ ≤ s.card / (8 : ℝ) ^ N := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ s)
        _ ≤ (M * 4 ^ (N + 1)) / (8 : ℝ) ^ N :=
          div_le_div_of_nonneg_right hscard (by positivity)
        _ = 4 * M * (1 / 2 : ℝ) ^ N := by
          calc
            _ = 4 * M * ((4 : ℝ) ^ N / (8 : ℝ) ^ N) := by ring
            _ = _ := by rw [← div_pow]; norm_num
    have he : (∑ x ∈ t, 1 / h x) + (∑ x ∈ u, 1 / h x) =
        ∑ x ∈ s, 1 / h x := Finset.sum_filter_add_sum_filter_not _ _ _
    rw [pow_succ]
    linarith

/-- A finite weighted-count lemma with geometric counting thresholds. Its
application below obtains the threshold counts from the proved curve theorem. -/
theorem sum_inv_height_le_of_geometric_count
    (hM : 0 ≤ M)
    (hheight : ∀ x ∈ s, 1 ≤ h x)
    (hcount : ∀ k : ℕ,
      ((s.filter (fun x => h x ≤ (8 : ℝ) ^ k)).card : ℝ) ≤ M * 4 ^ k) :
    ∑ x ∈ s, 1 / h x ≤ 9 * M := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (∑ x ∈ s, h x) (show (1 : ℝ) < 8 by norm_num)
  have hmax (x : α) (hx : x ∈ s) : h x ≤ (8 : ℝ) ^ N := by
    have hs := Finset.single_le_sum
      (fun y hy => (zero_le_one.trans (hheight y hy))) hx
    grind
  have hh := sum_inv_height_geometric_bound s h M hM N hheight hmax hcount
  have hnonneg : 0 ≤ 8 * M * (1 / 2 : ℝ) ^ N := by positivity
  linarith

end

lemma eight_pow_two_thirds (k : ℕ) :
    ((8 : ℝ) ^ k) ^ (2 / 3 : ℝ) = (4 : ℝ) ^ k := by
  have he : (8 : ℝ) ^ (2 / 3 : ℝ) = 4 := by nlinarith
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (k : ℝ),
    Real.rpow_mul_natCast (by norm_num), he]

