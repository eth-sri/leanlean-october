/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Noether.ClosedFormJet
public import CCDN.Noether.ShearNormalization
public import CCDN.ForMathlib.Matrix
import CCDN.Noether.FormalBranchOrder
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.PowerSeries.Inverse

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

private lemma bivariate_partials (f : MvPolynomial (Fin 2) K) :
    bivariatePolynomialEquiv K (pderiv 0 f) = (bivariatePolynomialEquiv K f).derivative ∧
    bivariatePolynomialEquiv K (pderiv 1 f) = bivariateCoefficientDerivative K (bivariatePolynomialEquiv K f) := by
  have hCin (a : K) : bivariateCoefficientDerivative K (Polynomial.C (Polynomial.C a)) = 0 := by
    ext i j; simp [Polynomial.coeff_C,apply_ite]
  have hX : bivariateCoefficientDerivative K Polynomial.X = 0 := by ext i j; simp [Polynomial.coeff_X,apply_ite]
  have hY : bivariateCoefficientDerivative K (Polynomial.C Polynomial.X) = 1 := by ext i j; simp [Polynomial.coeff_C,Polynomial.coeff_one,apply_ite]
  induction f using MvPolynomial.induction_on with
  | C a => simp [bivariatePolynomialEquiv_C,hCin]
  | add f g hf hg => simp [hf,hg]
  | mul_X f j hf =>
    fin_cases j <;> simp [Polynomial.derivative_mul,Derivation.leibniz,smul_eq_mul,hf,bivariatePolynomialEquiv_X_zero,bivariatePolynomialEquiv_X_one,hX,hY,mul_comm,add_comm]

private lemma grid_totalDegree_le (d : ℕ) (v : BivariateGrid d → K) : bivariateTotalDegree (bivariateGridPolynomial K d v) ≤ 2*d := by
  apply (bivariateTotalDegree_le_iff ..).mpr
  intro i j h
  have := not_imp_not.mpr (bivariateGridPolynomial_coeff_zero d v i j) h
  omega

/-- On the smooth branch with first partial nonzero, evaluation of the first numerator at the base point
is injective on the closed-form kernel. Indeed a zero value gives a zero jet longer than Bézout permits. -/
theorem minor_of_smooth_point (d : ℕ) (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (hz : eval z f = 0) (hs : eval z (pderiv 0 f) ≠ 0)
    (hdeg : (bivariatePolynomialEquiv K f).natDegree = d) (ht : f.totalDegree ≤ d) (hc : CharZeroOrGT K (2*d^2)) :
    (closedFormCoefficientMatrix d (bivariatePolynomialEquiv K f)).HasNonzeroMinor (2*d^2-1) := by
  classical
  let E := bivariatePolynomialEquiv K
  let M := closedFormCoefficientMatrix d (E f)
  let V := M.mulVecLin.ker
  let decode := closedFormPair K d
  let ev := (aeval z).toLinearMap.comp (E.symm.toLinearMap.comp ((LinearMap.fst K _ _).comp decode))
  let φ := ev.domRestrict V
  obtain ⟨ψ,hconst,param,faith⟩ := exists_faithful_formal_plane_branch f hf z 0 hz hs
  have hψ := (faith f).mpr dvd_rfl
  have hu : IsUnit (ψ (pderiv 0 f)) := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr (by rwa [hconst]))
  have kill (g : MvPolynomial (Fin 2) K) (hg : f ∣ g) (small : (E g).degree < d) : g = 0 := by
    by_contra hn
    have h := Polynomial.degree_le_of_dvd (map_dvd E hg) ((map_ne_zero_iff E E.injective).mpr hn)
    rw [Polynomial.degree_eq_natDegree ((map_ne_zero_iff E E.injective).mpr hf.ne_zero),hdeg] at h
    exact small.not_ge h
  have hinj : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp ((LinearMap.ker_eq_bot').mpr ?_)
    intro v he
    let p := E.symm (decode v.val).1
    let q := E.symm (decode v.val).2
    have hp : E p = (decode v.val).1 := E.apply_symm_apply _
    have hq : E q = (decode v.val).2 := E.apply_symm_apply _
    have hzero : eval z p = 0 := he
    have hclosed : pderiv 1 p*f-p*pderiv 1 f = pderiv 0 q*f-q*pderiv 0 f := by
      have hh := (closedFormCoefficientMatrix_kernel d (E f) v.val).mp (LinearMap.mem_ker.mp v.property)
      change bivariateCoefficientDerivative K (decode v.val).1 * E f - (decode v.val).1 * bivariateCoefficientDerivative K (E f) - (decode v.val).2.derivative* E f + (decode v.val).2*(E f).derivative = 0 at hh
      apply E.injective
      simp only [map_sub,map_mul,(bivariate_partials _).1,(bivariate_partials _).2,E] at hp hq ⊢
      rw [hp,hq]; linear_combination hh
    have hjet := closed_form_zero_jet f p q hclosed ψ hψ (z 1) param hu (by rwa [hconst]) hc
    have hpd : p.totalDegree ≤ 2*d := grid_totalDegree_le d (fun i => v.val (.inl i))
    have hp0 : p = 0 := by
      apply kill _ _ (hp ▸ bivariateGridPolynomial_degree_lt _)
      by_contra hnd
      have := formal_plane_vanishing_order_bound f hf ψ hψ 1 (z 1) param p hnd hjet
      nlinarith [Nat.mul_le_mul ht hpd]
    have hq0 : q = 0 := by
      apply kill _ ((faith q).mp ?_) (hq ▸ bivariateGridPolynomial_degree_lt _)
      have := congrArg ψ hclosed
      apply (mul_eq_zero.mp ?_).resolve_right hu.ne_zero
      simp only [map_sub,map_mul,hψ,hp0,map_zero,mul_zero,zero_mul] at this
      linear_combination this
    apply Subtype.ext
    apply closedFormPair_injective d
    change decode v.val = decode 0
    rw [map_zero]
    exact Prod.ext (by simpa [hp0] using hp.symm) (by simpa [hq0] using hq.symm)
  have hker := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_self] at hker
  have h := M.mulVecLin.finrank_range_add_finrank_ker
  have he : Module.finrank K (ClosedFormColumns d → K) = 2*d^2 := by simp [ClosedFormColumns,BivariateGrid,pow_two,two_mul]
  change M.rank + Module.finrank K V = _ at h
  apply Matrix.hasNonzeroMinor_of_le_rank
  change 2*d^2-1 ≤ M.rank
  omega

end
end CCDN
