/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.CharZeroOrGT
public import CCDN.Noether.BivariateTotalDegree
import CCDN.ForMathlib.Polynomial
import CCDN.Noether.BivariateFactorForms
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
Reducibility forces a rank drop of the closed-form coefficient matrix for normalized monic
bivariate equations whose degrees up to `d` are nonzero in the base field, in particular below
the characteristic and in characteristic zero. The rank drop is first derived from coprime
factor decompositions, with coprimality imposed in the univariate fraction-field ring, where
factorization can supply it.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- A reducible normalized equation of total degree at most d, with outer
degree d, in characteristic zero or larger than d, has coefficient-matrix kernel
dimension at least two. Both squarefree and repeated-factor cases are covered. -/
theorem closedForm_rank_drop_of_not_irreducible
    {F : Type*} [Field F] (d : ℕ) (hd : 0 < d)
    (hchar : CharZeroOrGT F d)
    (f : F[X][X]) (hf : f.Monic) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  have hextra (f0 p q : F[X][X]) (hf0 : bivariateTotalDegree f0 ≤ d) (hf0' : f0.derivative ≠ 0)
      (hp : InBivariateGrid d p) (hq : InBivariateGrid d q)
      (hclosed : closedFormOperator f0 (p, q) = 0)
      (hind : ∀ a : F, p ≠ C (C a) * f0.derivative) :
      (closedFormCoefficientMatrix d f0).rank + 2 ≤ 2 * d ^ 2 := by
    obtain ⟨hg₁, hg₂⟩ := bivariate_gradient_in_grid d hd f0 hf0
    refine closedForm_rank_drop_of_two_forms d f0
      (f0.derivative, (bivariateCoefficientDerivative F) f0) (p, q)
      hg₁ hg₂ hp hq (closedFormOperator_gradient f0) hclosed
      (fun he => hf0' (congrArg Prod.fst he)) fun a ha => hind a ?_
    have he := congrArg Prod.fst ha
    change a • f0.derivative = p at he
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using he.symm
  let φ := algebraMap F[X] (RatFunc F)
  have hinj := RatFunc.algebraMap_injective F
  obtain ⟨r, hr, s, hs⟩ :=
    WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos f (hdeg ▸ hd)) hf.ne_zero
  have hl : r.leadingCoeff * s.leadingCoeff = 1 := by rw [← leadingCoeff_mul, ← hs]; exact hf
  have ha := associated_mul_unit_right r (C s.leadingCoeff)
    (IsUnit.map C ⟨⟨s.leadingCoeff, r.leadingCoeff, by rw [mul_comm, hl], hl⟩, rfl⟩)
  let g := r * C s.leadingCoeff
  have hg : Irreducible g := ha.irreducible_iff.mp hr
  have hgm : g.Monic := by
    change (r * C s.leadingCoeff).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, hl]
  have hgf : g ∣ f := ha.dvd_iff_dvd_left.mp ⟨s, hs⟩
  obtain ⟨m, h, hnd, he⟩ := WfDvdMonoid.max_power_factor hf.ne_zero hg
  have hm : 0 < m := by
    by_contra hn
    obtain rfl : m = 0 := by omega
    simp only [pow_zero, one_mul] at he
    exact hnd (he ▸ hgf)
  have hhm : h.Monic := (hgm.pow m).of_mul_monic_left (he ▸ hf)
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hcop : IsCoprime (g.map φ) (h.map φ) :=
    (hgR.isCoprime_or_dvd _).resolve_right fun hdiv =>
      hnd ((hgm.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map (RatFunc F)).mpr hdiv)
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hgnat : (g.map φ).natDegree = g.natDegree := natDegree_map_eq_of_injective hinj _
  have hgd : 0 < bivariateTotalDegree g := hgpos.trans_le (bivariate_natDegree_le_totalDegree g)
  have hf_deriv : ∀ q : F[X][X], q.natDegree = d → q.derivative ≠ 0 := fun q hqd =>
    derivative_ne_zero_of_natCast_natDegree_ne_zero (by
      rw [hqd]; simpa using (map_ne_zero (algebraMap F (F[X]))).mpr (hchar d hd le_rfl))
  by_cases hm1 : m = 1
  · have he' : f = g * h := by simpa only [hm1, pow_one] using he
    have hhu : ¬IsUnit h := fun hhU =>
      hred (he' ▸ (associated_mul_unit_left g h hhU).irreducible_iff.mpr hg)
    have hhpos := hhm.natDegree_pos_of_not_isUnit hhu
    rw [he'] at hdeg htotal ⊢
    have hsum := natDegree_mul hg.ne_zero hhm.ne_zero
    have hhnat : (h.map φ).natDegree = h.natDegree := natDegree_map_eq_of_injective hinj _
    have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
      (separable_iff_derivative_ne_zero hgR).mpr
        (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
          rw [hgnat]; simpa using (map_ne_zero (algebraMap F (RatFunc F))).mpr (hchar _ hgpos (by omega))))
    have hh' := derivative_ne_zero_of_natCast_natDegree_ne_zero (f := h.map φ) (by
      rw [hhnat]; simpa using (map_ne_zero (algebraMap F (RatFunc F))).mpr (hchar _ hhpos (by omega)))
    obtain ⟨hpgrid, hqgrid⟩ := bivariate_factor_form_in_grid d g h hg.ne_zero hhm.ne_zero hgd htotal
    refine hextra (g * h) (h * g.derivative) (h * (bivariateCoefficientDerivative F) g) htotal
      (hf_deriv _ hdeg) hpgrid hqgrid ?_ fun a ha => ?_
    · change _ - _ - _ + _ = (0 : F[X][X]); linear_combination bivariate_factor_closed_form g h
    · exact factor_numerator_not_scalar_gradient (g.map φ) (h.map φ)
        (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg hh' (algebraMap F (RatFunc F) a)
        (by simpa only [Polynomial.map_mul, Polynomial.map_C, derivative_map, derivative_mul,
          Polynomial.map_add, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using
          congrArg (Polynomial.map φ) ha)
  · let k := m - 2
    have hm2 : m = k + 2 := by omega
    rw [hm2] at he
    rw [he] at hdeg htotal ⊢
    have hfn : g ^ (k + 2) * h ≠ 0 := mul_ne_zero (pow_ne_zero _ hg.ne_zero) hhm.ne_zero
    have hgle := natDegree_le_of_dvd (dvd_mul_of_dvd_left (dvd_pow_self g (by omega)) h) hfn
    have hgg : IsCoprime (g.map φ) (g.map φ).derivative :=
      (separable_iff_derivative_ne_zero hgR).mpr
        (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
          rw [hgnat]; simpa using (map_ne_zero (algebraMap F (RatFunc F))).mpr (hchar _ hgpos (by omega))))
    obtain ⟨hpgrid, hqgrid⟩ :=
      bivariate_power_factor_form_in_grid d k g h hg.ne_zero hhm.ne_zero hgd htotal
    refine hextra (g ^ (k + 2) * h) (g ^ k * h * g.derivative)
      (g ^ k * h * (bivariateCoefficientDerivative F) g) htotal
      (hf_deriv _ hdeg) hpgrid hqgrid ?_ fun a ha => ?_
    · change _ - _ - _ + _ = (0 : F[X][X]); linear_combination bivariate_power_factor_closed_form g h k
    · apply power_factor_numerator_not_scalar_gradient (g.map φ) (h.map φ) k
        (natDegree_pos_iff_degree_pos.mp (hgnat ▸ hgpos)) hcop hgg (algebraMap F (RatFunc F) a)
      rw [show (g.map φ) ^ (k + 2) * h.map φ = (g ^ (k + 2) * h).map φ by simp,
        Polynomial.derivative_map (g ^ (k + 2) * h) φ]
      simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, derivative_map,
        RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using congrArg (Polynomial.map φ) ha

end
end CCDN
