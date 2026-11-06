/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialLinearDescent
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Homogeneous coefficient descent and homogeneous top factors. -/

namespace CCDN
section
open MvPolynomial

section
variable {k K : Type*} [Field k] [Field K] [Algebra k K] {n d : ℕ}

/-- Applying a linear map `φ : K → k` to the coefficients of a homogeneous polynomial of
degree `d` gives a homogeneous polynomial of degree `d`. -/
lemma polynomialCoefficientLinear_homogeneous
    (φ : K →ₗ[k] k) (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    (polynomialCoefficientLinear φ f).IsHomogeneous d := by
  intro m hm
  apply hf
  intro hzero
  apply hm
  rw [polynomialCoefficientLinear_coeff, hzero, map_zero]

/-- A nonzero homogeneous polynomial `f` of degree `d` over an extension field `K` of `k` yields
a nonzero homogeneous polynomial `g` of degree `d` over `k` that vanishes at every `k`-point
where `f` vanishes. -/
theorem exists_nonzero_homogeneous_linear_descent
    (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) (hhom : f.IsHomogeneous d) :
    ∃ g : MvPolynomial (Fin n) k, g ≠ 0 ∧ g.IsHomogeneous d ∧
      ∀ x : Fin n → k, eval (algebraMap k K ∘ x) f = 0 → eval x g = 0 := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  refine ⟨polynomialCoefficientLinear φ f, ?_,
    polynomialCoefficientLinear_homogeneous φ f hhom, ?_⟩
  · intro he
    have hh := polynomialCoefficientLinear_coeff φ f m
    simp_all
  · intro x hx
    rw [polynomialCoefficientLinear_eval, hx, map_zero]

end

variable {K σ : Type*}

/-- The homogeneous component of `g * h` in degree `g.totalDegree + h.totalDegree` is the
product of the top-degree homogeneous components of `g` and `h`. -/
lemma top_homogeneousComponent_mul [CommRing K]
    (g h : MvPolynomial σ K) :
    homogeneousComponent (g.totalDegree + h.totalDegree) (g * h) =
      homogeneousComponent g.totalDegree g * homogeneousComponent h.totalDegree h := by
  calc
    _ = homogeneousComponent (g.totalDegree + h.totalDegree)
        ((∑ i ∈ Finset.range (g.totalDegree + 1), homogeneousComponent i g) * h) := by
      rw [sum_homogeneousComponent]
    _ = ∑ i ∈ Finset.range (g.totalDegree + 1),
        homogeneousComponent (g.totalDegree + h.totalDegree) (homogeneousComponent i g * h) := by
      rw [Finset.sum_mul, map_sum]
    _ = homogeneousComponent (g.totalDegree + h.totalDegree)
        (homogeneousComponent g.totalDegree g * h) := by
      apply Finset.sum_eq_single g.totalDegree
      · intro i hi hne
        have hi' : i < g.totalDegree := by grind
        apply homogeneousComponent_eq_zero
        have hh := totalDegree_mul (homogeneousComponent i g) h
        have hh' := (homogeneousComponent_isHomogeneous i g).totalDegree_le
        omega
      · grind
    _ = _ := homogeneousComponent_mul_of_isHomogeneous_left
      (homogeneousComponent_isHomogeneous _ _) h _

/-- A factorization of a homogeneous equation can be replaced by homogeneous
factors of the same respective total degrees. -/
theorem homogeneous_factorization_top [Field K]
    {f g h : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (he : f = g * h) :
    g.totalDegree + h.totalDegree = d ∧
      f = homogeneousComponent g.totalDegree g * homogeneousComponent h.totalDegree h := by
  have hd : g.totalDegree + h.totalDegree = d := by
    rw [← totalDegree_mul_of_isDomain hg hh, ← he, hf.totalDegree hf0]
  refine ⟨hd, ?_⟩
  rw [← top_homogeneousComponent_mul, ← he, hd, homogeneousComponent_eq_self hf]

