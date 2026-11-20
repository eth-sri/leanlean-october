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

section

variable {F : Type*} [Field F]
include F

/-- A bounded extra solution outside the scalar gradient span forces rank drop. -/
private theorem closedForm_rank_drop_of_extra_form
    (d : ℕ) (hd : 0 < d) (f p q : F[X][X])
    (hf : bivariateTotalDegree f ≤ d) (hf' : f.derivative ≠ 0)
    (hp : InBivariateGrid d p) (hq : InBivariateGrid d q)
    (hclosed : closedFormOperator f (p,q) = 0)
    (hind : ∀ a : F, p ≠ C (C a) * f.derivative) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨hg₁, hg₂⟩ := bivariate_gradient_in_grid d hd f hf
  apply closedForm_rank_drop_of_two_forms d f
    (f.derivative, (bivariateCoefficientDerivative F) f) (p,q)
    hg₁ hg₂ hp hq (closedFormOperator_gradient f) hclosed
  simp_all
  · intro a ha
    apply hind a
    have he := congrArg Prod.fst ha
    change a • f.derivative = p at he
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply] using he.symm

end

section

variable {F : Type*} [Field F]
  (f : F[X][X]) (hf : f.Monic) (hu : ¬IsUnit f)
include F f hf hu

private lemma exists_monic_bivariate_irreducible_factor :
    ∃ g : F[X][X], Irreducible g ∧ g.Monic ∧ g ∣ f := by
  obtain ⟨r, hr, hrf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf.ne_zero
  obtain ⟨s, hs⟩ := hrf
  have hl : r.leadingCoeff * s.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hs]
    exact hf
  have hsU : IsUnit s.leadingCoeff :=
    ⟨⟨s.leadingCoeff, r.leadingCoeff, by grind, hl⟩, rfl⟩
  have ha := associated_mul_unit_right r (C s.leadingCoeff) (hsU.map C)
  refine ⟨r * C s.leadingCoeff, ha.irreducible_iff.mp hr, ?_, ?_⟩
  · change (r * C s.leadingCoeff).leadingCoeff = 1
    rw [leadingCoeff_mul, leadingCoeff_C, hl]
  · exact ha.dvd_iff_dvd_left.mp ⟨s, hs⟩

/-- Extract one monic irreducible factor with its full multiplicity; the
remaining factor is monic and coprime after passage to the fraction field. -/
private lemma exists_monic_bivariate_primary_factor :
    ∃ (g h : F[X][X]) (m : ℕ), Irreducible g ∧ g.Monic ∧ h.Monic ∧
      0 < m ∧ f = g ^ m * h ∧
      IsCoprime (g.map (algebraMap F[X] (RatFunc F)))
        (h.map (algebraMap F[X] (RatFunc F))) := by
  obtain ⟨g, hg, hgm, hgf⟩ := exists_monic_bivariate_irreducible_factor f hf hu
  obtain ⟨m, h, hnd, he⟩ := WfDvdMonoid.max_power_factor hf.ne_zero hg
  have hm : 0 < m := by
    by_contra hn
    simp_all
  refine ⟨g, h, m, hg, hgm, ((hgm.pow m).of_mul_monic_left (he ▸ hf)), hm, he, ?_⟩
  apply ((hgm.irreducible_iff_irreducible_map_fraction_map.mp hg).isCoprime_or_dvd _).resolve_right
  intro hdiv
  exact hnd ((hgm.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map (RatFunc F)).mpr hdiv)

end

/-- A reducible normalized equation of total degree at most d, with outer
degree d, in characteristic zero or larger than d, has coefficient-matrix kernel
dimension at least two. Both squarefree and repeated-factor cases are covered. -/
theorem closedForm_rank_drop_of_not_irreducible
    {F : Type*} [Field F] (d : ℕ) (hd : 0 < d)
    (hchar : CharZeroOrGT F d)
    (f : F[X][X]) (hf : f.Monic) (hred : ¬Irreducible f)
    (hdeg : f.natDegree = d) (htotal : bivariateTotalDegree f ≤ d) :
    (closedFormCoefficientMatrix d f).rank + 2 ≤ 2 * d ^ 2 := by
  obtain ⟨g, h, m, hg, hgm, hhm, hm, he, hcop⟩ :=
    exists_monic_bivariate_primary_factor f hf (not_isUnit_of_natDegree_pos f (hdeg ▸ hd))
  let φ := algebraMap F[X] (RatFunc F)
  have hder (q : F[X][X]) (hq : 0 < q.natDegree) (hle : q.natDegree ≤ d) :
      (q.map φ).derivative ≠ 0 := by
    apply derivative_ne_zero_of_natCast_natDegree_ne_zero
    rw [natDegree_map_eq_of_injective (RatFunc.algebraMap_injective F)]
    exact (hchar.map (algebraMap F (RatFunc F))).natCast_ne_zero hq.ne' hle
  have hgpos := hgm.natDegree_pos_of_not_isUnit hg.not_isUnit
  have hgdvd : g ∣ f := he ▸ dvd_mul_of_dvd_left (dvd_pow_self g hm.ne') h
  have hgle := natDegree_le_of_dvd hgdvd hf.ne_zero
  have hgR : Irreducible (g.map φ) := hgm.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hgg := (separable_iff_derivative_ne_zero hgR).mpr (hder g hgpos (hgle.trans_eq hdeg))
  have ht' : bivariateTotalDegree (g * h) ≤ d := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    have hh := htotal
    rw [he, pow_succ', mul_right_comm, bivariateTotalDegree_mul _ _
      (mul_ne_zero hg.ne_zero hhm.ne_zero) (pow_ne_zero _ hg.ne_zero)] at hh
    omega
  obtain ⟨hp, hq⟩ := bivariate_factor_form_in_grid d g h hg.ne_zero hhm.ne_zero
    (hgpos.trans_le (bivariate_natDegree_le_totalDegree g)) ht'
  apply closedForm_rank_drop_of_extra_form d hd f _ _ htotal
    (derivative_ne_zero_of_natCast_natDegree_ne_zero (by
      rw [hdeg]
      exact (hchar.map (algebraMap F F[X])).natCast_ne_zero hd.ne' le_rfl)) hp hq
    (he.symm ▸ bivariate_factor_closed_form g h m)
  intro a ha
  have hae : h.map φ * (g.map φ).derivative =
      C (algebraMap F (RatFunc F) a) * ((g.map φ) ^ m * h.map φ).derivative := by
    have he' := congrArg (Polynomial.map φ) (ha.trans (congrArg (fun f => C (C a) * f.derivative) he))
    simpa only [Polynomial.map_mul, Polynomial.map_C, ← derivative_map, Polynomial.map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C, φ] using he'
  by_cases hm1 : m = 1
  · have hhpos := hhm.natDegree_pos_of_not_isUnit (fun hh => hred (by
      rw [he, hm1, pow_one]
      exact (associated_mul_unit_left g h hh).irreducible_iff.mpr hg))
    have hhle := natDegree_le_of_dvd (he ▸ dvd_mul_left h (g ^ m)) hf.ne_zero
    exact factor_numerator_not_scalar_gradient (g.map φ) (h.map φ)
      (natDegree_pos_iff_degree_pos.mp ((hgm.natDegree_map φ).symm ▸ hgpos))
      hcop hgg (hder h hhpos (hhle.trans_eq hdeg)) _ (by simpa only [hm1, pow_one] using hae)
  · have hdiv : g.map φ ∣ h.map φ * (g.map φ).derivative := by
      rw [hae, derivative_mul, derivative_pow]
      have hp : g.map φ ∣ (g.map φ) ^ (m - 1) := dvd_pow_self _ (by omega)
      exact dvd_mul_of_dvd_right (dvd_add
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp _) _) _)
        (dvd_mul_of_dvd_left (dvd_pow_self _ hm.ne') _)) _
    exact hgR.not_isUnit ((hcop.mul_right hgg).isUnit_of_dvd hdiv)

end
end CCDN
