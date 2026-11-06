/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import ArithmeticHeights.BombieriVaaler
import CCDN.Algebra.HomogeneousMonomials
import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.Height.IntegerCoefficientHeight
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.HomogeneousRank
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Algebra.RowSelection
import CCDN.AuxiliaryPolynomial.CoefficientBound
import CCDN.Determinant.HomogeneousDeterminantComparison

/-!
Bounded rational zeros either admit a degree-d auxiliary nonmultiple,
or control the defining equation's coefficient height by an explicit
finite-dimensional interpolation bound.

Bombieri--Vaaler for complete homogeneous evaluation matrices. The defining
equation supplies rank deficiency, and selected rows span the whole point set.
-/

namespace CCDN
open MvPolynomial Matrix

variable {B : ℝ}

/-- A quantitative coefficient-height dichotomy on the complete bounded
projective zero set. The height branch has log(H)<=N log(N)+d N log(B). -/
theorem projective_coefficient_height_dichotomy {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
        ((n + d).choose d : ℝ) * d * Real.log B ∨
    ∃ g, IsProjectiveAuxiliary f g d B := by
  let S := projectivePoints (projectiveZeroLocus (map (Int.castRingHom ℚ) f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 1) := fun i => primitiveProjectiveRep (e i).val
  have hz (i) : eval (z i) f = 0 :=
    (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
  have hbox (i j) : |(z i j : ℝ)| ≤ B :=
    (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e i).property).1
  by_cases hrel : ∀ g : MvPolynomial (Fin (n + 1)) ℤ, g.IsHomogeneous d →
      (∀ i, eval (z i) g = 0) → f ∣ g
  · left
    obtain ⟨s, a, hi, hspan, hs⟩ := homogeneous_independent_evaluation_rows f hf hf0 le_rfl z hz
    let N := (n + d).choose d
    let A := evaluationMatrix (homogeneousMonomials n d) (z ∘ a)
    obtain ⟨v, hv, hAv, hsmall⟩ :=
      Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hi (by simp_all)
    simp at hsmall
    let g := polynomialOfCoefficients (homogeneousMonomials n d) v
    have hgh := polynomialOfCoefficients_homogeneous n d v
    have hgz (i) : eval (z i) g = 0 := by
      apply vanishes_of_evaluation_row_mem_span _ (z ∘ a) v hAv (z i)
      rw [hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    let H := (integerCoefficientHeight f : ℝ)
    let R := (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / (Int.Matrix.minorGcd A : ℝ)) ^ (((N : ℝ) - s)⁻¹)
    have hD1 : (1 : ℝ) ≤ (Int.Matrix.minorGcd A : ℝ) := by
      exact_mod_cast Int.Matrix.one_le_minorGcd hi
    have hD0 : (0 : ℝ) < (Int.Matrix.minorGcd A : ℝ) := by linarith
    have hR : 0 ≤ R := Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) hD0.le) _
    have hH1 : 1 ≤ H := by dsimp [H]; exact_mod_cast integerCoefficientHeight_pos f hf0
    have hHb := integerCoefficientHeight_le f hR (fun m =>
      (show |(f.coeff m : ℝ)| ≤ |(g.coeff m : ℝ)| by
          obtain ⟨q, he⟩ := (hrel g hgh hgz)
          have hf0 : f ≠ 0 := fun h => (polynomialOfCoefficients_ne_zero _ (homogeneousMonomials_injective n d) hv) (by grind)
          have hq0 : q ≠ 0 := fun h => (polynomialOfCoefficients_ne_zero _ (homogeneousMonomials_injective n d) hv) (by grind)
          have hqdegree : q.totalDegree = 0 := by
            have hh := totalDegree_mul_of_isDomain hf0 hq0
            rw [← he, hf.totalDegree hf0, hgh.totalDegree (polynomialOfCoefficients_ne_zero _ (homogeneousMonomials_injective n d) hv)] at hh
            omega
          have hq := totalDegree_eq_zero_iff_eq_C.mp hqdegree
          have he' := calc
            g = f * q := he
            _ = f * C (q.coeff 0) := congrArg (f * ·) hq
            _ = C (q.coeff 0) * f := mul_comm _ _
          exact integer_scalar_factor_coefficient_bound (by grind) he' m).trans
        (abs_coefficient_polynomialOfCoefficients_le _ (homogeneousMonomials_injective n d) v hR
          (fun j => by
            have hj := le_ciSup (Set.finite_range (fun k => |v k|)).bddAbove j
            have hjR : |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) := mod_cast hj
            grind) m))
    have hNs : (1 : ℝ) ≤ N - s := by
      have hh := hs
      have hhR : (s : ℝ) + 1 ≤ N := mod_cast hh
      linarith
    obtain ⟨hGram, hcomp⟩ := log_gcd_le_of_coefficient_bound (by linarith : 0 < H) hD0
      (by grind) hHb
    have hN := lt_of_le_of_lt (Nat.zero_le s) hs
    have hN1 : (1 : ℝ) ≤ N := mod_cast hN
    have hlogH := Real.log_nonneg hH1
    have hlogN := Real.log_nonneg hN1
    have hlogB := Real.log_nonneg hB
    have hlogD := Real.log_nonneg hD1
    have hmulH := mul_le_mul_of_nonneg_right hNs hlogH
    have harch := evaluation_log_gram_le hN (homogeneousMonomials n d) (z ∘ a)
      hB (fun i j => hbox (a i) j) (fun j => (homogeneousMonomials_degree n d j).le) hGram
    have hfact : (s.factorial : ℝ) ≤ (N : ℝ) ^ s := by
      exact_mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left hs.le s)
    have hlogfact : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log (N : ℝ) := by
      have hh := Real.log_le_log (by positivity) hfact
      simp_all
    have hsN : (s : ℝ) ≤ N := mod_cast hs.le
    have hlast1 := mul_le_mul_of_nonneg_right hsN hlogN
    have hlast2 := mul_le_mul_of_nonneg_right hsN
      (mul_nonneg (Nat.cast_nonneg d) hlogB)
    nlinarith
  · right
    push Not at hrel
    obtain ⟨g, hgh, hgz, hgnd⟩ := hrel
    refine ⟨g, fun h => hgnd (by simp_all), hgh, ?_, hgnd⟩
    intro x hxB hxf
    let xS : S := ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
    obtain ⟨i, hi⟩ := e.surjective xS
    have hh := hgz i
    dsimp [z] at hh
    rw [hi] at hh
    exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

