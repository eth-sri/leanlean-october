/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import ArithmeticHeights.BombieriVaaler
public import CCDN.Algebra.HomogeneousMonomials
public import CCDN.AuxiliaryPolynomial.Nonmultiple
public import CCDN.Height.IntegerCoefficientHeight
import CCDN.Algebra.HomogeneousEvaluation
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Algebra.RowSelection
import CCDN.Determinant.HomogeneousDeterminantComparison

/-!
Bounded rational zeros either admit a degree-d auxiliary nonmultiple,
or control the defining equation's coefficient height by an explicit
finite-dimensional interpolation bound.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- A quantitative coefficient-height dichotomy on the complete bounded
projective zero set. The height branch has log(H)<=N log(N)+d N log(B). -/
theorem projective_coefficient_height_dichotomy {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      ((n + d).choose d : ℝ) * Real.log ((n + d).choose d) +
        ((n + d).choose d : ℝ) * d * Real.log B ∨
    ∃ g, IsProjectiveAuxiliary f g d B := by
  classical
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
    let N := (n + d).choose d
    let H := (integerCoefficientHeight f : ℝ)
    have hH1 : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf0
    obtain ⟨m, hm_supp, hm_sup⟩ :=
      Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf0) (fun m => (f.coeff m).natAbs)
    have hm_deg : m.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hf (mem_support_iff.mp hm_supp)
    obtain ⟨j, hj⟩ := homogeneousMonomials_surjective n d m hm_deg
    obtain ⟨col, π, hcol, hdet⟩ := det_multipleBasisVec_same_degree f j
    have hH_eq : H = |(f.coeff (homogeneousMonomials n d j) : ℝ)| := by
      dsimp [H, integerCoefficientHeight]
      rw [hm_sup, hj, Nat.cast_natAbs, Int.cast_abs]
    obtain ⟨s, a, _, hs, _, hi, hlog⟩ :=
      homogeneous_no_auxiliary_box_comparison_of_minor f hf hf0 le_rfl z hz hB hbox hrel
        (by linarith : 0 < H) ⟨col, π, hcol, by rw [hdet, hH_eq]; push_cast; rw [abs_pow]⟩
    have hNs : (1 : ℝ) ≤ (N : ℝ) - s := by
      have : (s : ℝ) + 1 ≤ N := mod_cast hs; linarith
    have hN1 : (1 : ℝ) ≤ N := mod_cast (lt_of_le_of_lt (Nat.zero_le s) hs)
    have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH1
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
    have hlogD : 0 ≤ Real.log (Int.Matrix.minorGcd
        (evaluationMatrix (homogeneousMonomials n d) (z ∘ a)) : ℝ) :=
      Real.log_nonneg (mod_cast Int.Matrix.one_le_minorGcd hi)
    have hmulH := mul_le_mul_of_nonneg_right hNs hlogH
    have hfact : (s.factorial : ℝ) ≤ (N : ℝ) ^ s :=
      mod_cast (Nat.factorial_le_pow s).trans (Nat.pow_le_pow_left hs.le s)
    have hlogfact : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log (N : ℝ) := by
      simpa only [Real.log_pow] using Real.log_le_log (mod_cast Nat.factorial_pos s) hfact
    have hsN : (s : ℝ) ≤ N := mod_cast hs.le
    have hlast1 := mul_le_mul_of_nonneg_right hsN hlogN
    have hlast2 := mul_le_mul_of_nonneg_right hsN
      (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlogB)
    change Real.log H ≤ (N : ℝ) * Real.log N + N * d * Real.log B
    nlinarith
  · right
    push Not at hrel
    obtain ⟨g, hgh, hgz, hgnd⟩ := hrel
    refine ⟨g, fun h => hgnd (by rw [h]; exact dvd_zero _), hgh, fun x hxB hxf => ?_, hgnd⟩
    obtain ⟨i, hi⟩ := e.surjective ⟨x, mem_projectivePoints.mpr ⟨hxB, hxf⟩⟩
    have hh := hgz i
    dsimp only [z] at hh
    rw [hi] at hh
    exact (mem_integer_projectiveZeroLocus hgh x).mpr hh

end
end CCDN
