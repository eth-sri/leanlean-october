/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.IntegralAffineLine
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
open MvPolynomial

/-- Corrected CCDN Proposition 4.3.3 for a finite set of rational
affine lines. Absolute irreducibility of the leading form supplies the
parallel-line bound inside the proof. The constant is chosen before the
surface, its degree, the radius and the family of lines. -/
theorem surface_line_contribution :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ,
      HasAbsIrreducibleTopForm f →
      3 ≤ f.totalDegree →
      ∀ (B : ℝ), 0 ≤ B →
      ∀ s : Finset (Set (RatPoint 3)),
      (∀ L ∈ s, ∃ a v, L = rationalAffineLine a v) →
      (∀ L ∈ s, L ⊆ zeroLocus (map (Int.castRingHom ℚ) f)) →
      (∑ L ∈ s, (count L B : ℝ)) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card ∧
      (count (⋃ L ∈ s, L) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
  classical
  obtain ⟨K, hK, hweight⟩ := integer_projective_plane_reciprocal_height_sum
  refine ⟨4 * K, by positivity, ?_⟩
  intro f hir hd B hB s hlines hsurface
  let t := s.filter (fun L => 1 < count L B)
  have hdir (L : Set (RatPoint 3)) (hL : L ∈ t) :=
    surface_line_projective_direction f L (hlines L (Finset.mem_filter.mp hL).1)
      (hsurface L (Finset.mem_filter.mp hL).1) hB (Finset.mem_filter.mp hL).2
  let p : Set (RatPoint 3) → ProjectivePoint 2 := fun L =>
    if hL : L ∈ t then (hdir L hL).choose else Classical.choice inferInstance
  have hp (L : Set (RatPoint 3)) (hL : L ∈ t) :
      p L ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) (homogeneousComponent f.totalDegree f)) ∧
      0 < (p L).mulHeight ∧ (p L).mulHeight ≤ 2 * B ∧
      (∃ a, L = rationalAffineLine a (p L).rep) ∧
      (count L B : ℝ) ≤ 4 * B / (p L).mulHeight := by
    simpa only [p, dite_eq_left hL] using (hdir L hL).choose_spec
  have hfib (q : ProjectivePoint 2) :
      ((t.filter (fun L => p L = q)).card : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 := by
    have hc := surface_parallel_lines_card_le f hir (by omega) q.rep q.rep_nonzero
      (t.filter (fun L => p L = q))
      (fun L hL => by
        obtain ⟨hLt, he⟩ := Finset.mem_filter.mp hL
        simpa only [he] using (hp L hLt).2.2.2.1)
      (fun L hL => hsurface L (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).1)
    exact_mod_cast hc.trans (by nlinarith [Nat.sub_le f.totalDegree 1])
  have himage : ∑ q ∈ t.image p, 1 / q.mulHeight ≤ K * (f.totalDegree : ℝ) ^ 4 :=
    hweight f.totalDegree hd (homogeneousComponent f.totalDegree f)
      (homogeneousComponent_isHomogeneous _ _) hir _ fun q hq => by
        obtain ⟨L, hLt, rfl⟩ := Finset.mem_image.mp hq; exact (hp L hLt).1
  have hsum : ∑ L ∈ t, 1 / (p L).mulHeight ≤ K * (f.totalDegree : ℝ) ^ 6 := calc
    _ = ∑ q ∈ t.image p, ∑ L ∈ t.filter (fun L => p L = q), 1 / (p L).mulHeight :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem p hx) _).symm
    _ ≤ ∑ q ∈ t.image p, (f.totalDegree : ℝ) ^ 2 * (1 / q.mulHeight) :=
      Finset.sum_le_sum fun q _ =>
        ((Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]).trans
          (by simp)).trans_le (mul_le_mul_of_nonneg_right (hfib q) (by positivity))
    _ = (f.totalDegree : ℝ) ^ 2 * ∑ q ∈ t.image p, 1 / q.mulHeight := (Finset.mul_sum _ _ _).symm
    _ ≤ (f.totalDegree : ℝ) ^ 2 * (K * (f.totalDegree : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left himage (by positivity)
    _ = _ := by ring
  have hgood : ∑ L ∈ t, (count L B : ℝ) ≤ (4 * K) * (f.totalDegree : ℝ) ^ 6 * B := calc
    _ ≤ ∑ L ∈ t, 4 * B / (p L).mulHeight := Finset.sum_le_sum fun L hL => (hp L hL).2.2.2.2
    _ = 4 * B * ∑ L ∈ t, 1 / (p L).mulHeight := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ 4 * B * (K * (f.totalDegree : ℝ) ^ 6) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring
  have hbad : ∑ L ∈ s.filter (fun L => ¬1 < count L B), (count L B : ℝ) ≤ s.card := calc
    _ ≤ ∑ _L ∈ s.filter (fun L => ¬1 < count L B), (1 : ℝ) := Finset.sum_le_sum fun L hL =>
      mod_cast (Nat.le_of_not_gt (Finset.mem_filter.mp hL).2 : count L B ≤ 1)
    _ = ((s.filter (fun L => ¬1 < count L B)).card : ℝ) := by simp
    _ ≤ s.card := mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hall : ∑ L ∈ s, (count L B : ℝ) ≤ (4 * K) * (f.totalDegree : ℝ) ^ 6 * B + s.card := by
    have he := Finset.sum_filter_add_sum_filter_not s (fun L => 1 < count L B)
      (fun L => (count L B : ℝ))
    linarith
  exact ⟨hall, (by exact_mod_cast count_biUnion_finset_le s (fun L => L) B :
    (count (⋃ L ∈ s, L) B : ℝ) ≤ ∑ L ∈ s, (count L B : ℝ)).trans hall⟩

end
end CCDN
