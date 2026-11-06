/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.EulerClosedFormRank
import CCDN.Noether.BivariateFactorForms
import CCDN.Noether.ClosedFormScaling
import CCDN.Noether.EulerPairRange

/-! Degree-correct logarithmic factor forms for the Euler-restricted
operator. The construction works in every characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The logarithmic factor pair of `g` and `h` with weights `a` and `b`: the pair `(P, Q)` with
`(P dx + Q dy) / (g * h) = b • dg / g - a • dh / h`, so `P = b • h * ∂ₓg - a • g * ∂ₓh` for the
outer derivative `∂ₓ` and `Q = b • h * ∂ᵧg - a • g * ∂ᵧh` for the inner derivative `∂ᵧ`. -/
def eulerFactorPair {R : Type*} [CommRing R] (a b : ℕ)
    (g h : R[X][X]) : R[X][X] × R[X][X] :=
  ((b : R) • (h * g.derivative) - (a : R) • (g * h.derivative),
   (b : R) • (h * (bivariateCoefficientDerivative R) g) -
     (a : R) • (g * (bivariateCoefficientDerivative R) h))

/-- If `g` and `h` have total degrees at most `a` and `b` with `a, b > 0` and `a + b = k + 2`, and
their logarithmic factor pair is nonzero, then the Euler closed-form operator of `g * h` has a
nonzero kernel vector in `EulerPairSpace F k`. -/
theorem exists_eulerFactorKernel {F : Type*} [Field F]
    (k a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = k + 2)
    (g h : F[X][X]) (hg : bivariateTotalDegree g ≤ a)
    (hh : bivariateTotalDegree h ≤ b)
    (hne : eulerFactorPair a b g h ≠ 0) :
    ∃ u : EulerPairSpace F k, u ≠ 0 ∧ eulerClosedFormOperator k (g * h) u = 0 := by
  have hsub (p q : F[X][X]) :
      bivariateTotalDegree (p - q) ≤ max (bivariateTotalDegree p) (bivariateTotalDegree q) := by
    unfold bivariateTotalDegree; rw [map_sub]; exact MvPolynomial.totalDegree_sub _ _
  have hdefect (d : ℕ) (f : F[X][X]) (hf : bivariateTotalDegree f ≤ d) :
      bivariateTotalDegree
        (bivariateEulerContraction F (f.derivative, (bivariateCoefficientDerivative F) f) -
          (d : F) • f) ≤ d - 1 := by
    rw [bivariateTotalDegree_le_iff]
    intro i j hij
    have hgrad : (((bivariateEulerContraction F
          (f.derivative, (bivariateCoefficientDerivative F) f)).coeff i).coeff j) =
          ((i + j : ℕ) : F) * (f.coeff i).coeff j := by
      change ((X * f.derivative + C X * (bivariateCoefficientDerivative F) f).coeff i).coeff j = _
      cases i with
      | zero =>
        simp only [coeff_add, coeff_X_mul_zero, zero_add, coeff_C_mul,
          coeff_bivariateCoefficientDerivative]
        cases j <;> [simp; (rw [coeff_X_mul, coeff_derivative]; push_cast; ring)]
      | succ i =>
        rw [coeff_add, coeff_X_mul, coeff_derivative, coeff_C_mul, coeff_add,
          coeff_bivariateCoefficientDerivative, show (i : F[X]) + 1 = C ((i : F) + 1) by simp,
          coeff_mul_C]
        cases j <;> [simp [mul_comm]; (rw [coeff_X_mul, coeff_derivative]; push_cast; ring)]
    rw [coeff_sub, coeff_sub, hgrad, coeff_smul, coeff_smul, smul_eq_mul] at hij
    have hc : (f.coeff i).coeff j ≠ 0 := fun hz => by simp [hz] at hij
    have hh := (bivariateTotalDegree_coeff_le f i j hc).trans hf
    have hne : i + j ≠ d := fun he => by rw [he, sub_self] at hij; exact hij rfl
    omega
  have hpart (s t : F[X][X]) (c e : ℕ) (hc : 0 < c)
      (hs : bivariateTotalDegree s ≤ c) (ht : bivariateTotalDegree t ≤ e)
      (hce : c + e = k + 2) :
      bivariateTotalDegree (t * s.derivative) ≤ k + 1 ∧
        bivariateTotalDegree (t * (bivariateCoefficientDerivative F) s) ≤ k + 1 :=
    ⟨by have := bivariateTotalDegree_mul_le t s.derivative
        have := bivariateTotalDegree_outerDerivative_le s; omega,
     by have := bivariateTotalDegree_mul_le t ((bivariateCoefficientDerivative F) s)
        have := bivariateTotalDegree_innerDerivative_le s; omega⟩
  obtain ⟨hgp, hgq⟩ := hpart g h a b ha hg hh hab
  obtain ⟨hhp, hhq⟩ := hpart h g b a hb hh hg (by omega)
  have hp : bivariateTotalDegree (eulerFactorPair a b g h).1 ≤ k + 1 :=
    (hsub _ _).trans (max_le
      ((bivariateTotalDegree_smul_le _ _).trans hgp)
      ((bivariateTotalDegree_smul_le _ _).trans hhp))
  have hq : bivariateTotalDegree (eulerFactorPair a b g h).2 ≤ k + 1 :=
    (hsub _ _).trans (max_le
      ((bivariateTotalDegree_smul_le _ _).trans hgq)
      ((bivariateTotalDegree_smul_le _ _).trans hhq))
  have he : bivariateTotalDegree
      (bivariateEulerContraction F (eulerFactorPair a b g h)) ≤ k + 1 := by
    rw [show bivariateEulerContraction F (eulerFactorPair a b g h) =
        (b : F) • (h * (bivariateEulerContraction F
          (g.derivative, (bivariateCoefficientDerivative F) g) - (a : F) • g)) -
        (a : F) • (g * (bivariateEulerContraction F
          (h.derivative, (bivariateCoefficientDerivative F) h) - (b : F) • h)) by
      simp only [eulerFactorPair, bivariateEulerContraction, LinearMap.coe_mk, AddHom.coe_mk,
        bivariate_smul_eq_constant_mul]; ring]
    refine (hsub _ _).trans (max_le
      ((bivariateTotalDegree_smul_le _ _).trans ?_) ((bivariateTotalDegree_smul_le _ _).trans ?_))
    · have := bivariateTotalDegree_mul_le h
        (bivariateEulerContraction F (g.derivative, (bivariateCoefficientDerivative F) g) - (a : F) • g)
      have := hdefect a g hg; omega
    · have := bivariateTotalDegree_mul_le g
        (bivariateEulerContraction F (h.derivative, (bivariateCoefficientDerivative F) h) - (b : F) • h)
      have := hdefect b h hh; omega
  obtain ⟨u, hu⟩ := exists_eulerBivariatePair k _ _ hp hq he
  refine ⟨u, fun hz => hne (by rw [hz, map_zero] at hu; exact hu.symm), ?_⟩
  change closedFormOperator (g * h) (eulerBivariatePair F k u) = 0
  rw [hu]
  have hg' : closedFormOperator (g * h)
      (h * g.derivative, h * (bivariateCoefficientDerivative F) g) = 0 := by
    change _ - _ - _ + _ = (0 : F[X][X]); linear_combination bivariate_factor_closed_form g h
  have hh' : closedFormOperator (g * h)
      (g * h.derivative, g * (bivariateCoefficientDerivative F) h) = 0 := by
    rw [mul_comm g h]; change _ - _ - _ + _ = (0 : F[X][X])
    linear_combination bivariate_factor_closed_form h g
  change closedFormOperator (g * h)
    ((b : F) • (h * g.derivative, h * (bivariateCoefficientDerivative F) g) -
      (a : F) • (g * h.derivative, g * (bivariateCoefficientDerivative F) h)) = 0
  rw [map_sub, map_smul, map_smul, hg', hh', smul_zero, smul_zero, sub_self]

end
end CCDN
