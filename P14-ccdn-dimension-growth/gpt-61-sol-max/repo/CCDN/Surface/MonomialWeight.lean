/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Hilbert.PrincipalStandardMonomials
public import Mathlib.Analysis.Real.Sqrt
import CCDN.Analysis.SurfaceMonomialWeightNumerics
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import CCDN.ForMathlib.MvPolynomial
import CCDN.Hilbert.PlaneHilbert
import Mathlib.Algebra.Order.Star.Real

/-! The sharp weighted degree of a full standard-monomial prefix for an
affine surface. The coefficient 2/3 of the square-root rank is retained,
with an explicit linear error depending only on the equation degree. -/

public section
namespace CCDN
open MvPolynomial Finset

/-- Standard monomials up to degree M have weighted degree at most
(2/3)s sqrt(2s/d)+(2d+2)s, where s is their cardinality and d is
the surface equation degree. -/
theorem surface_standard_monomial_weight {K : Type*} [Field K]
    (f : MvPolynomial (Fin 3) K) (hf : f ≠ 0) (hd : 0 < f.totalDegree)
    {M : ℕ} (hM : f.totalDegree ≤ M) :
    let S := standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex M
    (∑ a ∈ S, ((Finsupp.degree a : ℕ) : ℝ)) ≤
      (2 / 3 : ℝ) * S.card * Real.sqrt (2 * S.card / ↑f.totalDegree) +
        (2 * f.totalDegree + 2) * S.card := by
  classical
  dsimp only
  let H := fun k => Module.finrank K (filteredCoordinateSpace (Ideal.span {f}) k)
  have hrank (k : ℕ) (hk : f.totalDegree ≤ k) :
      H k + (2 + 1 + (k - f.totalDegree)).choose (k - f.totalDegree) =
        (2 + 1 + k).choose k := by
    simpa only [H, finrank_restrictTotalDegree, Fintype.card_fin] using
      principal_filtered_finrank f hf hk
  have hbounds (k : ℕ) (hk : f.totalDegree ≤ k) :
      ↑f.totalDegree * ((k : ℝ) - f.totalDegree + 1) ^ 2 / 2 ≤ H k ∧
        (H k : ℝ) ≤ ↑f.totalDegree * (↑k + 2) ^ 2 / 2 := by
    solve_by_elim [hypersurface_rank_power_bounds]
  have hsum := surface_rank_prefix_sum_lower H hM (fun k hk => (hbounds k hk).1)
  have hid := standardMonomialPrefix_weight_identity (Ideal.span {f}) M
  have hidR :
      (∑ a ∈ standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex M,
        ((Finsupp.degree a : ℕ) : ℝ)) + (∑ k ∈ range M, (H k : ℝ)) = ↑M * H M := by
    exact_mod_cast hid
  have hdR : (0 : ℝ) < f.totalDegree := by exact_mod_cast hd
  have hMR : (f.totalDegree : ℝ) ≤ M := by exact_mod_cast hM
  have hbase : 0 ≤ 2 * (H M : ℝ) / ↑f.totalDegree := by positivity
  let R := Real.sqrt (2 * (H M : ℝ) / ↑f.totalDegree)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hroot : ↑f.totalDegree * R ^ 2 = 2 * H M := by
    dsimp only [R]
    rw [Real.sq_sqrt hbase]
    field_simp
  have hlo : ↑M - f.totalDegree ≤ R := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hdR).mpr
    have hb := (hbounds M hM).1
    nlinarith
  have hhi : R ≤ ↑M + 2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    apply (div_le_iff₀ hdR).mpr
    have hb := (hbounds M hM).2
    nlinarith
  have hw : (∑ a ∈ standardMonomialPrefix (Ideal.span {f}) MonomialOrder.degLex M,
      ((Finsupp.degree a : ℕ) : ℝ)) + ↑f.totalDegree *
        (↑M - f.totalDegree) ^ 3 / 6 ≤ ↑M * H M := by
    linarith
  have hh := surface_weight_root_bound hdR hMR (Nat.cast_nonneg (H M)) R hR
    hroot hlo hhi hw
  simpa only [standardMonomialPrefix_card, H, R] using hh

end CCDN
