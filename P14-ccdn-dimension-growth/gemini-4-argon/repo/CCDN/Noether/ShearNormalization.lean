/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
public import CCDN.Noether.LeadingDirection
public import CCDN.Noether.PlaneShear

/-! Bounded integral shears give full outer degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- Variable zero corresponds to the outer variable of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_X_zero {R : Type*} [CommRing R] :
    bivariatePolynomialEquiv R (MvPolynomial.X 0) = (X : R[X][X]) := by
  simp [bivariatePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

/-- Variable one corresponds to the inner variable of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_X_one {R : Type*} [CommRing R] :
    bivariatePolynomialEquiv R (MvPolynomial.X 1) = (C X : R[X][X]) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp

/-- Constants correspond to constants of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_C {R : Type*} [CommRing R] (a : R) :
    bivariatePolynomialEquiv R (MvPolynomial.C a) = C (C a) :=
  (bivariatePolynomialEquiv R).commutes a

/-- The integral shear in nested polynomial coordinates. -/
def bivariateShear (R : Type*) [CommRing R] (a : R) : R[X][X] ≃ₐ[R] R[X][X] :=
  (bivariatePolynomialEquiv R).symm.trans ((planeShear R a).trans (bivariatePolynomialEquiv R))

/-- A two-variable exponent vector `m` equals `Finsupp.cons i (Finsupp.single 0 j)` if and only if
its components are `i` and `j`. -/
lemma bivariate_exponent_eq_iff (m : Fin 2 →₀ ℕ) (i j : ℕ) :
    Finsupp.cons i (Finsupp.single 0 j) = m ↔ m 0 = i ∧ m 1 = j := by
  constructor
  · intro h
    have h₀ := congrArg (fun s : Fin 2 →₀ ℕ => s 0) h
    have h₁ := congrArg (fun s : Fin 2 →₀ ℕ => s (Fin.succ (0 : Fin 1))) h
    simp only [Finsupp.cons_zero] at h₀
    simp only [Finsupp.cons_succ, Finsupp.single_eq_same] at h₁
    exact ⟨h₀.symm, h₁.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact (bivariate_exponent_eq m).symm

/-- A plane shear preserves irreducibility of bivariate polynomials. -/
lemma bivariateShear_irreducible_iff {R : Type*} [CommRing R]
    (a : R) (f : R[X][X]) : Irreducible (bivariateShear R a f) ↔ Irreducible f :=
  MulEquiv.irreducible_iff (f := bivariateShear R a)

/-- Every nonzero integer plane equation admits a shear with parameter in
0,...,d whose outer degree is exactly its original total degree. -/
theorem exists_bounded_full_outer_shear (f : ℤ[X][X]) (hf : f ≠ 0) :
    ∃ a : ℕ, a ≤ bivariateTotalDegree f ∧
      (bivariateShear ℤ (a : ℤ) f).natDegree = bivariateTotalDegree f ∧
      bivariateTotalDegree (bivariateShear ℤ (a : ℤ) f) = bivariateTotalDegree f := by
  obtain ⟨a, ha, he⟩ := exists_bounded_leading_direction f hf
  have htot : bivariateTotalDegree (bivariateShear ℤ (a : ℤ) f) = bivariateTotalDegree f := by
    simp only [bivariateTotalDegree, bivariateShear, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply, planeShear_totalDegree]
  refine ⟨a, ha, ?_, htot⟩
  let axisHom : MvPolynomial (Fin 2) ℤ →+* ℤ[X] :=
    MvPolynomial.eval₂Hom C ![X, C (a : ℤ) * X]
  have hlead_mono (m : Fin 2 →₀ ℕ) (c : ℤ) (d : ℕ) :
      leadingDirectionPolynomial (bivariatePolynomialEquiv ℤ (MvPolynomial.monomial m c)) d =
        if m 0 + m 1 = d then monomial (m 1) c else 0 := by
    by_cases hsum : m 0 + m 1 = d
    · rw [ite_eq_left hsum]
      ext j
      rw [leadingDirectionPolynomial_coeff, bivariatePolynomialEquiv_coeff, coeff_monomial]
      have he : m = Finsupp.cons (d - j) (Finsupp.single 0 j) ↔ m 1 = j := by
        rw [eq_comm, bivariate_exponent_eq_iff]; omega
      simp only [MvPolynomial.coeff_monomial, he]
      by_cases hj : m 1 = j
      · simp [hj, show j ≤ d by omega]
      · simp [hj]
    · rw [ite_eq_right hsum]
      ext j
      rw [leadingDirectionPolynomial_coeff, bivariatePolynomialEquiv_coeff, coeff_zero]
      by_cases hj : j ≤ d
      · have he : m ≠ Finsupp.cons (d - j) (Finsupp.single 0 j) := fun h =>
          hsum (by have := (bivariate_exponent_eq_iff m (d - j) j).mp h.symm; omega)
        simp [MvPolynomial.coeff_monomial, hj, he]
      · simp [hj]
  have haxis_coeff (p : MvPolynomial (Fin 2) ℤ) (d : ℕ) :
      (axisHom p).coeff d =
        (leadingDirectionPolynomial (bivariatePolynomialEquiv ℤ p) d).eval (a : ℤ) := by
    induction p using MvPolynomial.induction_on' with
    | add p g hp hg =>
      simp only [map_add, coeff_add, leadingDirectionPolynomial, Finset.sum_add_distrib,
        eval_add] at hp hg ⊢
      rw [hp, hg]
    | monomial m c =>
      have hmono : axisHom (MvPolynomial.monomial m c) =
          monomial (m 0 + m 1) (c * (a : ℤ) ^ m 1) := by
        change MvPolynomial.eval₂Hom C ![X, C (a : ℤ) * X] (MvPolynomial.monomial m c) = _
        rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        rw [← C_mul_X_pow_eq_monomial, mul_pow, ← map_pow, map_mul, pow_add]; ring
      rw [hmono, hlead_mono, coeff_monomial]
      split_ifs <;> simp [eval_monomial]
  have haxis : axisHom ((bivariatePolynomialEquiv ℤ).symm f) =
      Polynomial.map (Polynomial.evalRingHom 0) (bivariateShear ℤ (a : ℤ) f) := by
    suffices hh : axisHom =
        (Polynomial.mapRingHom (Polynomial.evalRingHom 0)).comp
          ((bivariatePolynomialEquiv ℤ).toRingHom.comp (planeShear ℤ (a : ℤ)).toRingHom) from
      congrArg (fun h : MvPolynomial (Fin 2) ℤ →+* ℤ[X] => h ((bivariatePolynomialEquiv ℤ).symm f)) hh
    apply MvPolynomial.ringHom_ext
    · intro c; simp [axisHom, planeShear, planeShearHom]
    · intro i; fin_cases i <;>
        simp [axisHom, planeShear, planeShearHom,
          bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_X_one]
  have h := congrArg (fun q : ℤ[X] => q.coeff (bivariateTotalDegree f)) haxis
  rw [haxis_coeff, AlgEquiv.apply_symm_apply, coeff_map] at h
  change (leadingDirectionPolynomial f (bivariateTotalDegree f)).eval (a : ℤ) =
    Polynomial.eval 0 ((bivariateShear ℤ (a : ℤ) f).coeff (bivariateTotalDegree f)) at h
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h
  have hp : (bivariateShear ℤ (a : ℤ) f).coeff (bivariateTotalDegree f) ≠ 0 := fun hz =>
    he (by rw [h, hz, coeff_zero])
  have hlo := le_natDegree_of_ne_zero hp
  have hhi := (bivariate_natDegree_le_totalDegree (bivariateShear ℤ (a : ℤ) f)).trans_eq htot
  omega

/-- The identification of two-variable polynomials with nested polynomials commutes with applying a
coefficient ring homomorphism. -/
lemma bivariatePolynomialEquiv_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    bivariateMap φ (bivariatePolynomialEquiv R f) =
      bivariatePolynomialEquiv S (MvPolynomial.map φ f) := by
  ext i j
  simp only [bivariateMap_coeff, bivariatePolynomialEquiv_coeff, MvPolynomial.coeff_map]

/-- The nested plane shear corresponds to the plane shear of two-variable polynomials. -/
lemma bivariateShear_equiv {R : Type*} [CommRing R]
    (a : R) (f : MvPolynomial (Fin 2) R) :
    bivariateShear R a (bivariatePolynomialEquiv R f) =
      bivariatePolynomialEquiv R (planeShear R a f) := by
  simp only [bivariateShear, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- Applying a coefficient ring homomorphism `φ` commutes with shearing, the shear parameter `a`
becoming `φ a`. -/
lemma bivariateShear_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (f : R[X][X]) :
    bivariateMap φ (bivariateShear R a f) =
      bivariateShear S (φ a) (bivariateMap φ f) := by
  obtain ⟨g, rfl⟩ := (bivariatePolynomialEquiv R).surjective f
  simp only [bivariateShear_equiv, bivariatePolynomialEquiv_map, planeShear_map]

/-- Shearing does not change the set of bad primes, including reductions
where the degree drops. -/
theorem bivariateBadReduction_shear_iff (a : ℤ) (f : ℤ[X][X]) (d p : ℕ) :
    BivariateBadReduction (bivariateShear ℤ a f) d p ↔ BivariateBadReduction f d p := by
  refine exists_congr fun hp => ?_
  let : Fact p.Prime := ⟨hp⟩
  change bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p)))
    (bivariateShear ℤ a f)) ≠ d ∨ ¬Irreducible
      (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) (bivariateShear ℤ a f)) ↔ _
  rw [bivariateShear_map, show bivariateTotalDegree
      (bivariateShear (AlgebraicClosure (ZMod p)) _ _) =
      bivariateTotalDegree (bivariateMap (Int.castRingHom (AlgebraicClosure (ZMod p))) f) by
    simp only [bivariateTotalDegree, bivariateShear, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply, planeShear_totalDegree], bivariateShear_irreducible_iff]

end
end CCDN
