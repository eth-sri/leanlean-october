/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateTotalDegree
import CCDN.Noether.BivariateFactorForms
import CCDN.ForMathlib.Polynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

variable {F : Type*} [Field F]

private def numerator (g h : F[X][X]) := (h*g.derivative, h*(bivariateCoefficientDerivative F) g)

private lemma numerator_closed (g h : F[X][X]) (m : ℕ) :
    closedFormOperator (g^m*h) (numerator g h) = 0 := by
  simp [closedFormOperator,numerator,Derivation.leibniz,derivative_mul,derivative_pow,
    Derivation.leibniz_pow,derivative_bivariateCoefficientDerivative,smul_eq_mul]
  ring

/-- In a squarefree factorization use `dg/g` and `dh/h`. If `g² | f`
instead use `dg/g` and `dg/g²`, which differ by the nonconstant factor `g`. -/
theorem closedForm_rank_drop_of_not_irreducible (d : ℕ) (hd : 0 < d) (char : CharZeroOrGT F d)
    (f : F[X][X]) (mon : f.Monic) (red : ¬ Irreducible f) (deg : f.natDegree = d)
    (total : bivariateTotalDegree f ≤ d) : (closedFormCoefficientMatrix d f).rank + 2 ≤ 2*d^2 := by
  obtain ⟨g,hg,h,he⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos f (deg ▸ hd)) mon.ne_zero
  subst f
  have hh : h ≠ 0 := by rintro rfl; simp at mon
  have lc : IsUnit g.leadingCoeff ∧ IsUnit h.leadingCoeff := (Commute.all _ _).isUnit_mul_iff.mp (by rw [← leadingCoeff_mul,mon.leadingCoeff]; exact isUnit_one)
  have pos (u : F[X][X]) (huc : IsUnit u.leadingCoeff) (hu : ¬IsUnit u) : 0 < u.natDegree := by
    by_contra! hz
    have e := Nat.eq_zero_of_le_zero hz
    rw [leadingCoeff,e] at huc
    exact hu ((eq_C_of_natDegree_eq_zero e).symm ▸ huc.map C)
  have gp := pos g lc.1 hg.not_isUnit
  have hp := pos h lc.2 (fun hU => red ((associated_mul_unit_right _ _ hU).irreducible_iff.mp hg))
  rw [natDegree_mul hg.ne_zero hh] at deg
  have diff (u : F[X][X]) (h0 : 0<u.natDegree) (hle : u.natDegree ≤ d) : u.derivative ≠ 0 :=
    derivative_ne_zero_of_natCast_natDegree_ne_zero (by simpa using (map_ne_zero (algebraMap F F[X])).mpr (char _ h0 hle))
  have gd := diff g gp (by omega)
  have gT := gp.trans_le (bivariate_natDegree_le_totalDegree g)
  obtain ⟨u1,u2⟩ := bivariate_factor_form_in_grid d g h hg.ne_zero hh gT total
  have closed := numerator_closed g h 1
  rw [pow_one] at closed
  by_cases div : g ∣ h
  · obtain ⟨k,rfl⟩ := div
    have hk : k ≠ 0 := by grind
    have gt : bivariateTotalDegree (g*k) ≤ bivariateTotalDegree (g*(g*k)) := by
      unfold bivariateTotalDegree
      exact MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd _ (dvd_mul_left (g*k) g)) (by aesop)
    obtain ⟨v1,v2⟩ := bivariate_factor_form_in_grid d g k hg.ne_zero hk gT (by omega)
    refine closedForm_rank_drop_of_two_forms d _ (numerator g k) (numerator g (g*k)) v1 v2 u1 u2 ?_ closed ?_ ?_
    · simpa [pow_two,mul_assoc] using numerator_closed g k 2
    · exact fun he => mul_ne_zero hk gd (congrArg Prod.fst he)
    · intro a he
      have hh := congrArg Prod.fst he
      change a • (k*g.derivative) = g*k*g.derivative at hh
      rw [Algebra.smul_def, mul_assoc g] at hh
      have e := mul_right_cancel₀ (mul_ne_zero hk gd) hh
      have eqg : g = C (C a) := e.symm
      simp [eqg] at gp
  · obtain ⟨v1,v2⟩ := bivariate_factor_form_in_grid d h g hh hg.ne_zero (hp.trans_le (bivariate_natDegree_le_totalDegree h)) (mul_comm g h ▸ total)
    refine closedForm_rank_drop_of_two_forms d _ (numerator h g) (numerator g h) v1 v2 u1 u2 ?_ closed ?_ ?_
    · simpa [mul_comm h g] using numerator_closed h g 1
    · exact fun he => mul_ne_zero hg.ne_zero (diff h hp (by omega)) (congrArg Prod.fst he)
    · intro a he
      have hh := congrArg Prod.fst he
      change a • (g*h.derivative) = h*g.derivative at hh
      have hdiv : g ∣ h*g.derivative := hh ▸ (by rw [Algebra.smul_def]; exact dvd_mul_of_dvd_right (dvd_mul_right ..) _)
      have hdvd := (hg.prime.dvd_or_dvd hdiv).resolve_left div
      exact (not_lt_of_ge (natDegree_le_of_dvd hdvd gd)) (natDegree_derivative_lt gp.ne')

end
end CCDN
