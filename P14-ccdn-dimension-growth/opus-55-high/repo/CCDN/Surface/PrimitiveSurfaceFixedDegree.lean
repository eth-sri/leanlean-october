/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Height.Box
import CCDN.Height.PrimitiveIntegerPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Surface.CoefficientReduction
import CCDN.Surface.ResidueLinearCount
import CCDN.Surface.RetainedCurveCount
import CCDN.Surface.SmallCurveCover
import CCDN.Surface.TopFormBadPrimes
import Mathlib.Algebra.Order.Star.Real

/-! A coefficient-uniform linear bound for primitive affine surface
polynomials of each fixed degree at least five. The argument constructs
its congruence auxiliaries and curve cover. -/

namespace CCDN
section
open MvPolynomial Finset

/-- For each degree `d ≥ 5`, there is a constant `C` such that every primitive integer
surface equation of degree `d` with absolutely irreducible top-degree form has at most `C B`
integral points of height at most `B` on its zero set, for every `B ≥ 1`. -/
theorem primitive_surface_fixed_degree_linear_bound (d : ℕ) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : MvPolynomial (Fin 3) ℤ, PrimitiveIntegerPolynomial f →
      HasAbsIrreducibleTopForm f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤ C * B := by
  let K := surfaceCoefficientLogConstant d
  have hK := (show 0 < surfaceCoefficientLogConstant d by
      have hh := Real.log_natCast_nonneg ((3 + d).choose d)
      unfold surfaceCoefficientLogConstant
      positivity).le
  let A := surfaceCongruenceDegreeConstant d K
  have hA := (surfaceCongruenceDegreeConstant_pos d K).le
  let A₀ := 2 * d * A
  have hA₀ : 0 ≤ A₀ := by positivity
  let D := A₀ * surfaceResidueLogScale d K
  have hlogscale : 1 ≤ surfaceResidueLogScale d K := by
    have hs := surfaceResidueWindowScale_two_le d hK
    have hp := scalingPrimeRatio_one_le
    have hl := Real.log_nonneg (by nlinarith)
    unfold surfaceResidueLogScale
    have hh : 0 ≤ (Real.log 4 + 4) * scalingPrimeRatio * surfaceResidueWindowScale d K := by
      positivity
    linarith
  have hD : 0 ≤ D := by nlinarith
  obtain ⟨Ccurve, hCcurve, hcurve⟩ := retained_surface_curve_union_bound
  obtain ⟨Cres, hCres, hres⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), f.totalDegree = d →
      ∀ B : ℝ, ∀ hB : 1 ≤ B, ∀ F : SurfaceCongruenceFamily f B A,
      Irreducible (MvPolynomial.map (Int.castRingHom ℚ) f) →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ S, IsSurfaceCurve (MvPolynomial.map (Int.castRingHom ℚ) f) I (δ I)) →
      (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
        (2 * B ^ (1 / Real.sqrt (d : ℝ))) (surfaceResidueWindow_one_le d hK hB)) B : ℝ) ≤
          C * B := by
    have hscale := surfaceResidueWindowScale_two_le d hK
    have hratio := scalingPrimeRatio_one_le
    have hdR : (5 : ℝ) ≤ d := mod_cast hd
    let U := scalingPrimeRatio * surfaceResidueWindowScale d K + 1
    have hU : 0 ≤ U := by nlinarith
    obtain ⟨C₀, hC₀, hbound⟩ := congruencePrimeWindow_surface_residual_bound
      (show 1 ≤ surfaceResidueWindowScale d K by linarith)
      (show 1 ≤ 2 * (d : ℝ) by linarith) 4
    let E := 8 * d * A ^ 2 * (surfaceResidueLogScale d K) ^ 2 * U ^ 2
    have hE : 0 ≤ E := by positivity
    refine ⟨E * C₀ + 1, by positivity, ?_⟩
    intro f hfd B hB F hir S δ hS
    have hB0 := zero_lt_one.trans_le hB
    have hlogB := Real.log_nonneg hB
    have hL := surfaceResidueWindow_one_le d hK hB
    have hpoly := surface_residue_residual_count_le F hA hB hL
      (by grind)
      (show 0 ≤ 2 * B ^ (1 / Real.sqrt (d : ℝ)) by positivity)
      (by rw [hfd]; nlinarith [Real.rpow_pos_of_pos hB0 (1 / Real.sqrt (d : ℝ))])
      hir S δ hS
    rw [hfd, surfaceResidueLogBudget_window] at hpoly
    have hu : scalingPrimeRatio * surfaceResidueWindow d K B + 1 ≤
        U * (Real.log B + 1) := by
      dsimp only [surfaceResidueWindow, U]
      nlinarith
    have hx : (2 * B ^ (1 / Real.sqrt d)) ^ 2 =
        4 * B ^ (2 / Real.sqrt d) := by
      rw [mul_pow, ← Real.rpow_natCast (B ^ (1 / Real.sqrt d)) 2,
        ← Real.rpow_mul hB0.le]
      norm_num only [Nat.cast_ofNat]
      congr 2
      ring
    rw [hx] at hpoly
    have hestimate :
        (count (surfaceResidueResidualLocus F S (surfaceResidueWindow d K B)
          (2 * B ^ (1 / Real.sqrt (d : ℝ))) hL) B : ℝ) ≤
        E * (((congruencePrimeWindow (surfaceResidueWindow d K B)).card *
          (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceResidueWindow d K B)).card) *
          B ^ (2 / Real.sqrt d) * (Real.log B + 1) ^ 4) := by
      calc
        _ ≤ _ := hpoly
        _ ≤ 2 * d * A ^ 2 *
            (surfaceResidueLogScale d K * (Real.log B + 1)) ^ 2 *
            (U * (Real.log B + 1)) ^ 2 *
            (4 * B ^ (2 / Real.sqrt (d : ℝ))) *
            (congruencePrimeWindow (surfaceResidueWindow d K B)).card *
            (2 * (d : ℝ)) ^ (congruencePrimeWindow (surfaceResidueWindow d K B)).card := by
          gcongr
        _ = _ := by grind
    have hh := mul_le_mul_of_nonneg_left (hbound d hd B hB) hE
    have hfinal :=
      hestimate.trans hh
    nlinarith
  let Cret := Ccurve * (d ^ 6 + A₀ * (D ^ 2 * (D + 1) + 1))
  have hCret : 0 ≤ Cret := by positivity
  refine ⟨12 * d ^ 2 + Cret + Cres + 1, by positivity, ?_⟩
  intro f hprim htop hfd B hB
  subst d
  have habs := absolute_irreducible_of_top_homogeneousComponent_irreducible f htop
  have hir := rational_irreducible_of_charZero_map f habs
  have hB0 := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  rcases primitive_surface_coefficient_reduction f hprim hir hB with hheight | hlarge
  · have hH : 1 ≤ (integerCoefficientHeight f : ℝ) := by
      exact_mod_cast integerCoefficientHeight_pos f (by aesop)
    have hheight' := hheight
    have hL := surfaceResidueWindow_one_le f.totalDegree hK hB
    obtain ⟨F, S, δ, hS, hbudget, hcover⟩ :=
      exists_surface_small_curve_residual_cover f habs (by omega) hK hheight'
        (isSurfaceResidueWindow_of_log_height (by omega) hK hB hH
          (coefficient_abs_le_integerCoefficientHeight f) hheight')
    let small := S.filter (fun I => (δ I : ℝ) ≤
      2 * f.totalDegree * A * surfaceResidueLogBudget B
        (surfaceResidueWindow f.totalDegree K B))
    have hsmall (I : Ideal (CoordinatePolynomial 3)) (hI : I ∈ small) :
        IsSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I) ∧ 0 < δ I :=
      ⟨(hS I (mem_filter.mp hI).1).toIsSurfaceCurve, (hS I (mem_filter.mp hI).1).pos⟩
    have hcap (I : Ideal (CoordinatePolynomial 3)) (hI : I ∈ small) :
        (δ I : ℝ) ≤ D * (Real.log B + 1) := by
      have hh := (mem_filter.mp hI).2
      rw [surfaceResidueLogBudget_window] at hh
      simpa [D, A₀, mul_assoc] using hh
    have hroot : 1 ≤ B ^ (1 / Real.sqrt f.totalDegree) :=
      Real.one_le_rpow hB (by positivity)
    have hbudget' : (∑ I ∈ small, (δ I : ℝ)) ≤
        A₀ * B ^ (1 / Real.sqrt f.totalDegree) * (Real.log B + 1) := by
      calc
        _ ≤ ∑ I ∈ S, (δ I : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by grind)
        _ ≤ f.totalDegree * A *
            (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := hbudget
        _ ≤ f.totalDegree * A *
            (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) * (1 + Real.log B) := by
          gcongr
          linarith
        _ = _ := by grind
    have hret :=
      hcurve f htop hd small δ A₀ D B hA₀ hD hB hsmall hcap hbudget'
    have hresidual := hres f rfl B hB F hir S δ (fun I hI => (hS I hI).toIsSurfaceCurve)
    have hsingular : (count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        9 * f.totalDegree ^ 2 * B := by
      have hh := singular_hypersurface_dimension_growth
        (map (Int.castRingHom ℚ) f) hir hB
      simpa [rational_map_totalDegree, Nat.cast_one, Nat.cast_ofNat, pow_one,
        show (3 * (1 + 2) : ℝ) = 9 by norm_num] using hh
    have hcoverR : (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
        (count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B : ℝ) +
          count (⋃ I ∈ small, idealZeroLocus I) B +
          count (surfaceResidueResidualLocus F S (surfaceResidueWindow f.totalDegree K B)
            (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) hL) B := by
      simpa [Nat.cast_add, small, A] using (Nat.cast_le).mpr hcover
    nlinarith
  · nlinarith

