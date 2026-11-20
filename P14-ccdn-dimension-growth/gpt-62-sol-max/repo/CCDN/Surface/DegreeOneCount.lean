/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Plane.IntegralAffineLine
public import CCDN.Statements
public import CCDN.Surface.CurveComponents
public import Mathlib.RingTheory.Ideal.Height
import CCDN.Curve.AffineCurveCount
import CCDN.Surface.LineContribution
import CCDN.Surface.NonlinearCount

/-! A common bound for a surface's finite curve cover separates the
line contribution from the nonlinear curve bounds. -/

@[expose] public section
namespace CCDN
open MvPolynomial
noncomputable section

/-- Separate lines from nonlinear curves, charging the additive cost of the lines
against the total degree budget. -/
theorem surface_curve_union_bound :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), HasAbsIrreducibleTopForm f → 3 ≤ f.totalDegree →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3))) (δ : Ideal (CoordinatePolynomial 3) → ℕ)
        (B : ℝ), 1 ≤ B → (∀ P ∈ S, IsSurfaceCurve (map (Int.castRingHom ℚ) f) P (δ P)) →
      (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤ C * (f.totalDegree : ℝ) ^ 6 * B +
        K * (∑ P ∈ S.filter (fun P => 2 ≤ δ P), curveBound (δ P) B) + ∑ P ∈ S, (δ P : ℝ) := by
  classical
  obtain ⟨C, hC, hline⟩ := surface_line_contribution
  obtain ⟨K, hK, hcurve⟩ := affine_curve_count 3 (by omega)
  refine ⟨C, K, hC, hK, ?_⟩
  intro f htop hd S δ B hB hS
  let L := S.filter (fun P => δ P = 1)
  let T := S.filter (fun P => 2 ≤ δ P)
  have hsplit : (⋃ P ∈ S, idealZeroLocus P) =
      (⋃ P ∈ L, idealZeroLocus P) ∪ (⋃ P ∈ T, idealZeroLocus P) := by
    ext x
    simp only [L, T, Set.mem_union, Set.mem_iUnion, Finset.mem_filter, exists_prop]
    constructor
    · rintro ⟨P, hP, hx⟩
      have hpos := (hS P hP).pos
      by_cases hδ : δ P = 1
      · exact Or.inl ⟨P, ⟨hP, hδ⟩, hx⟩
      · exact Or.inr ⟨P, ⟨hP, by omega⟩, hx⟩
    · rintro (⟨P, hP, hx⟩ | ⟨P, hP, hx⟩) <;> exact ⟨P, hP.1, hx⟩
  have hL := hline f htop hd B (by linarith) L (fun P hP => by
    obtain ⟨hPS, hδ⟩ := Finset.mem_filter.mp hP
    exact hδ ▸ hS P hPS)
  have hT : (count (⋃ P ∈ T, idealZeroLocus P) B : ℝ) ≤ K * ∑ P ∈ T, curveBound (δ P) B := by
    rw [Finset.mul_sum]
    refine (by exact_mod_cast count_biUnion_finset_le T idealZeroLocus B : _ ≤ ∑ P ∈ T, (count (idealZeroLocus P) B : ℝ)).trans
      (Finset.sum_le_sum fun P hP => ?_)
    obtain ⟨hPS, hδ⟩ := Finset.mem_filter.mp hP
    exact hcurve P (hS P hPS).isPrime (δ P) (by omega) (hS P hPS).degree B hB
  have hLcard : (L.card : ℝ) ≤ ∑ P ∈ S, (δ P : ℝ) := by
    calc
      _ = ∑ P ∈ L, (δ P : ℝ) := by
        simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
        exact Finset.sum_congr rfl (fun P hP => by simp [(Finset.mem_filter.mp hP).2])
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (by intros; positivity)
  rw [hsplit]
  have hsum : (count ((⋃ P ∈ L, idealZeroLocus P) ∪ (⋃ P ∈ T, idealZeroLocus P)) B : ℝ) ≤
      (count (⋃ P ∈ L, idealZeroLocus P) B : ℝ) + count (⋃ P ∈ T, idealZeroLocus P) B := by
    exact_mod_cast count_union_le _ _ B
  change _ ≤ _ + K * (∑ P ∈ T, curveBound (δ P) B) + _
  linarith

end
end CCDN
