/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.IntegralAffineLine
public import CCDN.Surface.CurveComponents
import CCDN.Plane.DegreeOneAffineLine
import CCDN.Surface.DirectionSum
import CCDN.Surface.LineDirections
import CCDN.Surface.NonlinearCount
import CCDN.Surface.ParallelLines

/-! Finite families of rational affine lines on a surface. Grouping
lines by their projective direction combines the primitive spacing bound
with the uniform reciprocal-height sum. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Weighted finite sums with a uniform bound on the cardinality of each
fiber. No injectivity of the indexing map is required. -/
private theorem sum_comp_le_fiber_card_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (p : α → β) (w : β → ℝ) (M : ℝ)
    (hw : ∀ q ∈ s.image p, 0 ≤ w q)
    (hfiber : ∀ q ∈ s.image p, ((s.filter (fun x => p x = q)).card : ℝ) ≤ M) :
    ∑ x ∈ s, w (p x) ≤ M * ∑ q ∈ s.image p, w q := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun _ => Finset.mem_image_of_mem p) w, Finset.mul_sum]
  simpa [nsmul_eq_mul] using sum_le_sum fun q hq => mul_le_mul_of_nonneg_right (hfiber q hq) (hw q hq)

/-- The sum over directions bounds the contribution of degree-one components. -/
theorem surface_line_contribution :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f → 3 ≤ f.totalDegree →
      ∀ (B : ℝ), 0 ≤ B → ∀ S : Finset (Ideal (CoordinatePolynomial 3)),
      (∀ P ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) P 1) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + S.card := by
  classical
  obtain ⟨K, hK, hweight⟩ := integer_projective_plane_reciprocal_height_sum
  refine ⟨4 * K, by positivity, ?_⟩
  intro f hir hd B hB S hcurves
  let t := S.filter (fun P => 1 < count (idealZeroLocus P) B)
  have hdir (P : Ideal (CoordinatePolynomial 3)) : ∃ p : ProjectivePoint 2, P ∈ t →
        p ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
        (∃ a, idealZeroLocus P = rationalAffineLine a p.rep) ∧
        (count (idealZeroLocus P) B : ℝ) ≤ 4 * B / p.mulHeight := by
    by_cases hP : P ∈ t
    swap
    · exact ⟨Classical.choice inferInstance, fun h => (hP h).elim⟩
    obtain ⟨hPS, hlarge⟩ := mem_filter.mp hP
    have hC := hcurves P hPS
    let := hC.isPrime
    obtain ⟨a, v, _, ha⟩ := (degree_one_zeroLocus_eq_rationalAffineLine P hC.degree).1
    exact (surface_line_projective_direction f _ ⟨a, v, ha⟩
      (fun _ hx => hx _ hC.mem) hlarge).imp (fun _ h _ => h)
  choose p hp using hdir
  have hfib (r : ProjectivePoint 2) (_hr : r ∈ t.image p) :
      ((t.filter (fun P => p P = r)).card : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by
    have hc := surface_parallel_lines_card_le f hir (by omega) r.rep r.rep_nonzero
      (t.filter (fun P => p P = r))
      (fun P hP => (mem_filter.mp hP).2 ▸ (hp P (mem_filter.mp hP).1).2.1)
      (fun P hP => hcurves P (mem_filter.mp (mem_filter.mp hP).1).1)
    exact_mod_cast hc.trans (by rw [pow_two]; gcongr; omega :
      f.totalDegree * (f.totalDegree - 1) ≤ f.totalDegree ^ 2)
  have himage : ∑ r ∈ t.image p, 1 / r.mulHeight ≤ K * (f.totalDegree : ℝ) ^ 4 := by
    apply hweight f.totalDegree hd (homogeneousComponent f.totalDegree f)
      (homogeneousComponent_isHomogeneous _ _) hir
    intro r hr
    obtain ⟨P, hPt, rfl⟩ := mem_image.mp hr
    exact (hp P hPt).1
  have hsum : ∑ P ∈ t, 1 / (p P).mulHeight ≤ K * (f.totalDegree : ℝ) ^ 6 := by
    calc
      _ ≤ (f.totalDegree : ℝ) ^ 2 * ∑ r ∈ t.image p, 1 / r.mulHeight :=
        sum_comp_le_fiber_card_mul t p (fun r => 1 / r.mulHeight) _ (fun _ _ => by positivity) hfib
      _ ≤ (f.totalDegree : ℝ) ^ 2 * (K * (f.totalDegree : ℝ) ^ 4) := by gcongr
      _ = _ := by ring
  have hterms (P) (hP : P ∈ S) : (count (idealZeroLocus P) B : ℝ) ≤
      1 + if 1 < count (idealZeroLocus P) B then 4 * B * (1 / (p P).mulHeight) else 0 := by
    split_ifs with h
    · rw [mul_one_div]
      exact (hp P (mem_filter.mpr ⟨hP, h⟩)).2.2.trans (le_add_of_nonneg_left zero_le_one)
    · simpa using (Nat.cast_le (α := ℝ).mpr (not_lt.mp h))

  have hall := sum_le_sum hterms
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, sum_ite,
    ← mul_sum] at hall
  have hc : (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ ∑ P ∈ S, (count (idealZeroLocus P) B : ℝ) := by
    exact_mod_cast count_biUnion_finset_le S idealZeroLocus B
  have hb := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * B by positivity)
  linarith [hc.trans hall, hb]

end
end CCDN
