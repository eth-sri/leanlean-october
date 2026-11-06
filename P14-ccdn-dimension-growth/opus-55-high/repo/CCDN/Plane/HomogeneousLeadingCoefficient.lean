/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.HomogeneousTranslation
import CCDN.Height.IntegerCoefficientHeight
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import CCDN.Algebra.HomogeneousChart
import CCDN.Plane.GridHeight

/-! Positioning a coefficient-height witness as the lexicographic leading
coefficient by a bounded integral translation of the affine chart. -/

namespace CCDN
section
open MvPolynomial
open scoped MonomialOrder

/-- Every exponent of total degree at most `d` is lexicographically at most the pure power
`x₀ ^ d` of the first variable. -/
lemma exponent_le_pure_first {n d : ℕ} (m : Fin (n + 1) →₀ ℕ)
    (hm : m.sum (fun _ e => e) ≤ d) : m ≼[MonomialOrder.lex] Finsupp.single 0 d := by
  have hs := exponent_degree_split m
  by_cases he : m 0 = d
  · have ht : chartExponent m = 0 := by
      apply (Finsupp.degree_eq_zero_iff _).mp
      change (chartExponent m).sum (fun _ e => e) = 0
      omega
    have hm' : m = Finsupp.single 0 d := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · grind
      · have h := congrArg (fun t => t j) ht
        simpa using h
    rw [hm']
  · apply le_of_lt
    change toLex m < toLex (Finsupp.single (0 : Fin (n + 1)) d)
    refine ⟨0, ?_, ?_⟩
    · grind
    · simp
      omega

section
variable {R : Type*} [CommRing R] {n d : ℕ}

/-- If `f` has total degree at most `d` and a nonzero coefficient at `x₀ ^ d`, then its
lexicographic leading coefficient is that coefficient. -/
lemma lex_leadingCoeff_eq_pure_first
    (f : MvPolynomial (Fin (n + 1)) R) (hd : f.totalDegree ≤ d)
    (hc : f.coeff (Finsupp.single 0 d) ≠ 0) :
    MonomialOrder.lex.leadingCoeff f = f.coeff (Finsupp.single 0 d) := by
  have he : MonomialOrder.lex.degree f = Finsupp.single 0 d := by
    apply MonomialOrder.lex.toSyn.injective
    apply le_antisymm
    · apply MonomialOrder.degree_le_iff.mpr
      intro m hm
      exact exponent_le_pure_first m ((le_totalDegree hm).trans hd)
    · exact MonomialOrder.lex.le_degree (mem_support_iff.mpr hc)
  change f.coeff (MonomialOrder.lex.degree f) = _
  rw [he]

lemma homogeneous_pure_first_coefficient
    (f : MvPolynomial (Fin (n + 1)) R) (hf : f.IsHomogeneous d) :
    f.coeff (Finsupp.single 0 d) = eval (Fin.cons 1 (0 : Fin n → R)) f := by
  obtain ⟨j, hj⟩ := homogeneousMonomials_surjective n d (Finsupp.single 0 d) (by simp)
  have hc := affineChart_homogeneous_coefficient f hf j
  rw [hj] at hc
  have ht : chartExponent (Finsupp.single (0 : Fin (n + 1)) d) = 0 := by aesop
  rw [ht] at hc
  rw [← affineChart_eval, eval_zero]
  exact hc.symm

/-- For `f` homogeneous of degree `d`, the coefficient of `x₀ ^ d` in the translate
`homogeneousTranslation R a f` is the value `f (1, a)`. -/
lemma homogeneousTranslation_pure_first
    (a : Fin n → R) (f : MvPolynomial (Fin (n + 1)) R) (hf : f.IsHomogeneous d) :
    (homogeneousTranslation R a f).coeff (Finsupp.single 0 d) = eval (Fin.cons 1 a) f := by
  rw [homogeneous_pure_first_coefficient _ (homogeneousTranslation_homogeneous a hf),
    homogeneousTranslation_eval_chart, zero_add]

end

