/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import ArithmeticHeights.BombieriVaaler
public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.AuxiliaryPolynomial.Nonmultiple
public import CCDN.Height.IntegerCoefficientHeight
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

public section
namespace CCDN
open MvPolynomial Matrix

/-- A homogeneous equation yields a small homogeneous polynomial
vanishing at every given integral point. -/
private theorem exists_small_homogeneous_vanishing_polynomial {n d M t : ℕ}
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (CCDN.IntPoint (n + 1))) (hzero : ∀ i, eval (points i) f = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), s < (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      ∃ g : CCDN.IntegerPolynomial (n + 1), g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (points i) g = 0) ∧ CoefficientHeightLE g
          ((Real.sqrt (((evaluationMatrix (homogeneousMonomials n M) (points ∘ a) *
            (evaluationMatrix (homogeneousMonomials n M) (points ∘ a))ᵀ).det : ℤ) : ℝ) /
            (Int.Matrix.minorGcd (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ)) ^
              ((((n + M).choose M : ℝ) - s)⁻¹)) := by
  classical
  obtain ⟨s, a, hli, hspan, hs⟩ :=
    homogeneous_independent_evaluation_rows f hf hf0 hdM points hzero
  let mon := homogeneousMonomials n M
  let A := evaluationMatrix mon (points ∘ a)
  obtain ⟨v, hv, hAv, hsmall⟩ :=
    Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hli (by simpa using hs)
  simp only [Fintype.card_fin] at hsmall
  refine ⟨s, a, hs, hli, polynomialOfCoefficients mon v,
    polynomialOfCoefficients_ne_zero mon (homogeneousMonomials_injective n M) hv,
    polynomialOfCoefficients_homogeneous n M v, ?_, ?_⟩
  · intro i
    apply vanishes_of_evaluation_row_mem_span mon (points ∘ a) v hAv (points i)
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  · apply abs_coefficient_polynomialOfCoefficients_le mon (homogeneousMonomials_injective n M) v
    · apply Real.rpow_nonneg
      have hD := Int.Matrix.one_le_minorGcd hli
      exact div_nonneg (Real.sqrt_nonneg _) (by positivity)
    · intro j
      have hj := le_ciSup (Set.finite_range (fun k => |v k|)).bddAbove j
      have hjR : |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) := by exact_mod_cast hj
      exact hjR.trans hsmall

end CCDN

namespace CCDN
open MvPolynomial Matrix

variable {n d : ℕ}

/-- If an integer form `f` of degree `d` divides a nonzero integer form `g` of the same degree,
then every coefficient of `f` is bounded in absolute value by the corresponding coefficient
of `g`, since `g` is a nonzero integer multiple of `f`. -/
lemma homogeneous_same_degree_coefficient_le_of_dvd 
    {f g : CCDN.IntegerPolynomial n} (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d)
    (hg0 : g ≠ 0) (hdiv : f ∣ g) (m : Fin n →₀ ℕ) :
    |(f.coeff m : ℝ)| ≤ |(g.coeff m : ℝ)| := by
  obtain ⟨q, he⟩ := hdiv
  have hf0 : f ≠ 0 := fun h => hg0 (by simp [he, h])
  have hq0 : q ≠ 0 := fun h => hg0 (by simp [he, h])
  have hqdegree : q.totalDegree = 0 := by
    have hh := totalDegree_mul_of_isDomain hf0 hq0
    rw [← he, hf.totalDegree hf0, hg.totalDegree hg0] at hh
    omega
  have hq := totalDegree_eq_zero_iff_eq_C.mp hqdegree
  have hc : q.coeff 0 ≠ 0 := by grind
  exact have he' := Trans.trans (Trans.trans he (congrArg ((HMul.hMul f)) hq)) (mul_comm f (C (q.coeff 0)));
  integer_scalar_factor_coefficient_bound hc he' m


/-- A quantitative coefficient-height dichotomy on the complete bounded
projective zero set. The height branch has log(H)<=N log(N)+d N log(B). -/
theorem projective_coefficient_height_dichotomy 
    (f : CCDN.IntegerPolynomial (n + 1)) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
        ((n + d).choose d : ℝ) * d * Real.log B ∨
    ∃ g, IsProjectiveAuxiliary f g d B := by
  classical
  let S := projectivePoints (projectiveZeroLocus (CCDN.rationalPolynomial f)) B
  let e := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 1) := fun i => primitiveProjectiveRep (e i).val
  have hz (i) : eval (z i) f = 0 :=
    (mem_integer_projectiveZeroLocus hf _).mp (mem_projectivePoints.mp (e i).property).2
  have hbox (i j) : |(z i j : ℝ)| ≤ B :=
    (primitiveProjectiveRep_bound _ j).trans (mem_projectivePoints.mp (e i).property).1
  by_cases hrel : ∀ g : CCDN.IntegerPolynomial (n + 1), g.IsHomogeneous d →
      (∀ i, eval (z i) g = 0) → f ∣ g
  · exact Or.inl ((by
                    obtain ⟨s, a, hs, hi, g, hg0, hgh, hgz, hc⟩ :=
                      exists_small_homogeneous_vanishing_polynomial f hf hf0 le_rfl z hz
                    let N := (n + d).choose d
                    let A := evaluationMatrix (homogeneousMonomials n d) (z ∘ a)
                    let H := (integerCoefficientHeight f : ℝ)
                    let R := (Real.sqrt (((A * Aᵀ).det : ℤ) : ℝ) / (Int.Matrix.minorGcd A : ℝ)) ^ (((N : ℝ) - s)⁻¹)
                    have hD1 : 1 ≤ (Int.Matrix.minorGcd A : ℝ) := by
                      exact_mod_cast Int.Matrix.one_le_minorGcd hi
                    have hD0 : 0 < (Int.Matrix.minorGcd A : ℝ) := by linarith
                    have hR : 0 ≤ R := Real.rpow_nonneg (div_nonneg (Real.sqrt_nonneg _) hD0.le) _
                    have hH1 : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf0
                    have hHb := integerCoefficientHeight_le f hR (fun m =>
                      (homogeneous_same_degree_coefficient_le_of_dvd hf hgh hg0 (hrel g hgh hgz) m).trans (hc m))
                    have hNs : 1 ≤ (N : ℝ) - s := by
                      have hh := hs
                      have hhR : (s : ℝ) + 1 ≤ N := by exact_mod_cast hh
                      linarith
                    obtain ⟨hGram, hcomp⟩ := log_gcd_le_of_coefficient_bound (by linarith : 0 < H) hD0
                      (by linarith : 0 < (N : ℝ) - s) hHb
                    have hN := lt_of_le_of_lt (Nat.zero_le s) hs
                    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
                    have hlogH := Real.log_nonneg hH1
                    have hlogN := Real.log_nonneg hN1
                    have hlogB := Real.log_nonneg hB
                    have hlogD := Real.log_nonneg hD1
                    have harch := evaluation_log_gram_le hN (homogeneousMonomials n d) (z ∘ a)
                      hB (fun i j => hbox (a i) j) (fun j => (homogeneousMonomials_degree n d j).le) hGram
                    have hfact : ↑s.factorial ≤ (N : ℝ) ^ s := by
                      exact_mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left hs.le s)
                    have hlogfact := by
                      have hh := Real.log_le_log (by positivity) hfact
                      rwa [Real.log_pow] at hh
                    have hsN : (s : ℝ) ≤ N := by exact_mod_cast hs.le
                    have hlast2 := mul_le_mul_of_nonneg_right hsN
                      (mul_nonneg (Nat.cast_nonneg  d) hlogB)
                    change Real.log H ≤ ↑N * Real.log N + N * d * Real.log B
                    nlinarith))
  · right
    push Not at hrel
    obtain ⟨g, hgh, hgz, hgnd⟩ := hrel
    refine ⟨g, hgh, ?_, hgnd⟩
    intro x hxB hxf
    let xS : S := ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
    obtain ⟨i, hi⟩ := e.surjective xS
    have hh := hgz i
    dsimp only [z] at hh
    rw [hi] at hh
    exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

end CCDN
