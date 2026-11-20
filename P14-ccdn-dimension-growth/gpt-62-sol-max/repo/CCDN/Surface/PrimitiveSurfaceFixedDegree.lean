/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.Box
public import CCDN.Height.PrimitiveIntegerPolynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Surface.CoefficientReduction
import CCDN.Surface.ResidueLinearCount
import CCDN.Surface.RetainedCurveCount
import CCDN.Surface.SmallCurveCover
import CCDN.Surface.TopFormBadPrimes
import Mathlib.Algebra.Order.Star.Real

/-! A coefficient-uniform linear bound for primitive affine surface
polynomials of each fixed degree at least five. The argument constructs
its congruence auxiliaries and curve cover. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- For each degree `d ≥ 5`, there is a constant `C` such that every primitive integer
surface equation of degree `d` with absolutely irreducible top-degree form has at most `C B`
integral points of height at most `B` on its zero set, for every `B ≥ 1`. -/
theorem primitive_surface_fixed_degree_linear_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ, PrimitiveIntegerPolynomial f →
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → 5 ≤ d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
  by_cases hd : 5 ≤ d
  swap
  · exact ⟨1, one_pos, fun _ _ _ _ h => (hd h).elim⟩
  let K := surfaceCoefficientLogConstant d
  have hK : 0 ≤ K := (surfaceCoefficientLogConstant_pos d).le
  let A := surfaceCongruenceDegreeConstant d K
  have hA : 0 ≤ A := (surfaceCongruenceDegreeConstant_pos d K).le
  let A₀ := 2 * (d : ℝ) * A
  have hA₀ : 0 ≤ A₀ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (40 * (4 * Real.log ((d : ℝ) + 1) + K + d) + 18)
  obtain ⟨U, hU, hwindow⟩ := exists_surface_prime_window N
  let D := A₀ * residueLogScale N U
  have hlogU := Real.log_nonneg hU
  have hD : 0 ≤ D := by positivity
  obtain ⟨Ccurve, hCcurve, hcurve⟩ := retained_surface_curve_union_bound
  obtain ⟨Cres, hCres, hres⟩ := surface_residue_linear_count d hd A U hA hU N
  let Cret := Ccurve * ((d : ℝ) ^ 6 + A₀ * (D ^ 2 * (D + 1) + 1))
  have hCret : 0 ≤ Cret := by positivity
  refine ⟨12 * (d : ℝ) ^ 2 + Cret + Cres + 1, by positivity, ?_⟩
  intro f hprim htop hfd _ B hB
  subst d
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f htop
  have hir := rational_irreducible_of_charZero_map f habs
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by rw [hz, map_zero])
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  rcases primitive_surface_coefficient_reduction f hprim hir hB with hheight | hlarge
  · have hH : 1 ≤ (integerCoefficientHeight f : ℝ) := by
      exact_mod_cast integerCoefficientHeight_pos f hf0
    obtain ⟨W, hcard, hprime, hp⟩ := hwindow B hB
    have hupper p hp' := (hp p hp').2
    have hW : IsSurfaceResidueWindow f B (integerCoefficientHeight f) W := by
      refine ⟨hB, hH, hd, coefficient_abs_le_integerCoefficientHeight f, hprime,
        fun p h => (hp p h).1, ?_⟩
      rw [hcard]
      have hlogd : 0 ≤ Real.log ((f.totalDegree : ℝ) + 1) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) f.totalDegree])
      nlinarith [mul_le_mul_of_nonneg_right hN (show 0 ≤ (Real.log B + 1) / 40 by positivity),
        mul_nonneg hlogd hlogB]
    obtain ⟨F, S, δ, hS, hbudget, hcover⟩ :=
      exists_surface_small_curve_residual_cover f habs (by omega) hK hheight hW
    let small := S.filter (fun I => (δ I : ℝ) ≤ 2 * f.totalDegree * A * surfaceResidueLogBudget B W)
    have hcap (I : Ideal (CoordinatePolynomial 3)) (hI : I ∈ small) :
        (δ I : ℝ) ≤ D * (Real.log B + 1) := by
      have hlogW := surfaceResidueLogBudget_le hB hU W hprime hupper
      rw [hcard] at hlogW
      exact ((mem_filter.mp hI).2).trans (by
        simpa [D, A₀, mul_assoc] using mul_le_mul_of_nonneg_left hlogW hA₀)
    let Y := B ^ (1 / Real.sqrt (f.totalDegree : ℝ))
    have hY : 1 ≤ Y := Real.one_le_rpow hB (by positivity)
    have hbudget' : (∑ I ∈ small, (δ I : ℝ)) ≤ A₀ * Y * (Real.log B + 1) := by
      refine ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hbudget).trans ?_
      change (f.totalDegree : ℝ) * A * (Y + 1) * (1 + Real.log B) ≤ _
      calc
        _ ≤ (f.totalDegree : ℝ) * A * (2 * Y) * (1 + Real.log B) := by
          gcongr
          linarith
        _ = _ := by dsimp [A₀]; ring
    have hret := hcurve f htop hd small δ A₀ D B hA₀ hD hB
      (fun I hI => (hS I (mem_filter.mp hI).1).toIsSurfaceCurve) hcap hbudget'
    change _ ≤ Cret * B at hret
    have hresidual := hres f rfl B hB W hcard hprime hupper F hir S δ (fun I hI => (hS I hI).toIsSurfaceCurve)
    have hsingular := singular_hypersurface_dimension_growth (n := 1)
      (map (Int.castRingHom ℚ) f) hir hB
    norm_num [rational_map_totalDegree] at hsingular
    have hcoverR := Nat.cast_le (α := ℝ).mpr hcover
    push_cast at hcoverR
    nlinarith only [hcoverR, hret, hresidual, hsingular,
      show 0 ≤ 3 * (f.totalDegree : ℝ) ^ 2 * B + B by positivity]

  · exact hlarge.trans (mul_le_mul_of_nonneg_right (by
      nlinarith only [hCret, hCres, sq_nonneg (f.totalDegree : ℝ)]) hB0.le)

end
end CCDN
